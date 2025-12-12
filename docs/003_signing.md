# Two-Round Threshold Signing

The signing protocol produces a threshold signature from partial contributions. It runs in two rounds with phase-indexed CRDT state. The first round commits to ephemeral nonces. The second round produces partial signatures. An aggregator combines the partials into a final signature.

## Module Structure

The signing implementation is split across focused modules for maintainability:

- **`Protocol/Sign/Types.lean`** - Core types: `SessionTracker`, `NonceRegistry`, message types (`SignCommitMsg`, `SignRevealWMsg`, `SignShareMsg`), error types (`SignError`), and output types (`Signature`, `SignatureDone`)

- **`Protocol/Sign/LocalRejection.lean`** - Local rejection sampling for norm bounds (eliminates global retry coordination)

- **`Protocol/Core/Abort.lean`** - Session-level abort coordination for liveness failures and security violations

- **`Protocol/Sign/Core.lean`** - Core functions: `lagrangeCoeffAtZero`, `lagrangeCoeffs`, `computeChallenge`, `aggregateSignature`, `aggregateSignatureLagrange`, `ValidSignTranscript`, `validateSigning`

- **`Protocol/Sign/Threshold.lean`** - Threshold support: `CoeffStrategy`, `strategyOK`, `SignMode`, `ThresholdCtx`, context constructors (`mkAllCtx`, `mkThresholdCtx`, `mkThresholdCtxComputed`), and context-based aggregation

- **`Protocol/Sign/Sign.lean`** - Re-exports from all submodules for backward compatibility

- **`Protocol/Sign/Session.lean`** - Session-typed API that makes nonce reuse a compile-time error

## Phase-Indexed State

The signing protocol uses phase-indexed state that forms a join-semilattice at each phase.

```lean
inductive Phase
  | commit
  | reveal
  | shares
  | done
```

Each phase carries accumulated data that can be merged with the join operation (⊔).

## Inputs

Each signing session requires the following inputs.

- **Message.** The message $m \in \mathcal{M}$ to be signed.
- **Signer set.** The active signing subset $S \subseteq \{1, \ldots, n\}$.
- **Secret shares.** Each party $P_i \in S$ holds its secret share $s_i$.
- **Public key.** All parties know the global public key $\mathsf{pk}$.
- **Public shares.** All parties know the public shares $\{\mathsf{pk}_j\}$ from key generation.

## Message Types

The protocol uses three message types across its phases.

```lean
structure SignCommitMsg (S : Scheme) where
  sender     : S.PartyId
  session    : Nat
  commitW    : S.Commitment  -- hash commitment to hiding nonce
  hidingVal  : S.Public      -- public hiding commitment W_hiding = A(hiding nonce)
  bindingVal : S.Public      -- public binding commitment W_binding = A(binding nonce)
  context    : ExternalContext := {}  -- for external protocol binding

structure SignRevealWMsg (S : Scheme) where
  sender  : S.PartyId
  session : Nat
  opening : S.Opening  -- opening for commitment verification
  context : ExternalContext := {}

structure SignShareMsg (S : Scheme) where
  sender  : S.PartyId
  session : Nat
  z_i     : S.Secret
  context : ExternalContext := {}  -- for external protocol binding
```

All message types include an optional `context` field for binding to external protocols. See [Protocol Integration](06_integration.md) for details.

## Dual Nonce Structure (FROST Pattern)

Following FROST, we use two nonces per signer instead of one:

- **Hiding nonce**: Protects against adaptive adversaries
- **Binding nonce**: Commits to the signing context (message + all commitments)

This provides stronger security against adaptive chosen-message attacks.

```lean
structure SigningNonces (S : Scheme) where
  hidingVal  : S.Secret   -- protects signer from adaptive adversaries
  bindingVal : S.Secret   -- commits to signing context

structure SigningCommitments (S : Scheme) where
  hidingVal  : S.Public   -- W_hiding = A(hiding nonce)
  bindingVal : S.Public   -- W_binding = A(binding nonce)
```

### Domain-Separated Hash Functions (FROST H4, H5)

Following FROST, the signing protocol uses domain-separated hash functions:

- **H4 (Message pre-hashing)**: `hashMessage` pre-hashes large messages before signing, using domain prefix `ice-nine-v1-msg`. This enables efficient signing of arbitrarily large messages.

- **H5 (Commitment list hashing)**: `hashCommitmentList` produces canonical encodings of commitment lists, using domain prefix `ice-nine-v1-com`. This ensures all parties compute identical binding factors.

```lean
def hashMessage (S : Scheme) (msg : S.Message) : ByteArray :=
  HashDomain.message ++ serializeMessage msg

def hashCommitmentList (S : Scheme) (commits : List (SignCommitMsg S)) : ByteArray :=
  HashDomain.commitmentList ++ encodeCommitmentList S commits
```

### Binding Factor Derivation

The binding factor $\rho_i$ binds each signer's nonce to the full signing context:

$$\rho_i = H_1(\text{msg}, \mathsf{pk}, \text{encoded\_commitments}, i)$$

where $H_1$ uses domain prefix `ice-nine-v1-rho`.

The effective nonce is then:

$$y_{\text{eff}} = y_{\text{hiding}} + \rho \cdot y_{\text{binding}}$$
$$w_{\text{eff}} = W_{\text{hiding}} + \rho \cdot W_{\text{binding}}$$

This prevents an adversary from adaptively choosing the message after seeing nonce commitments.

## Party State

Each party $P_i$ maintains local state during signing.

```lean
structure SignLocalState (S : Scheme) where
  share   : KeyShare S             -- party's long-term credential from DKG
  msg     : S.Message              -- message being signed
  session : Nat                    -- unique session identifier
  nonces  : SigningNonces S        -- dual ephemeral nonces (NEVER reuse!)
  commits : SigningCommitments S   -- public nonce commitments
  openW   : S.Opening              -- commitment randomness for hiding commitment
```

The local state contains:
- The ephemeral nonces $(y_{\text{hiding}}, y_{\text{binding}}) \in \mathcal{S}^2$ sampled for this session.
- The public commitments $W_{\text{hiding}} = A(y_{\text{hiding}})$ and $W_{\text{binding}} = A(y_{\text{binding}})$.
- The commitment opening $\rho \in \mathcal{O}$.
- The session identifier for binding.

## Round 1: Nonce Commitment

In round one each party commits to an ephemeral nonce. This commitment prevents adaptive attacks where an adversary chooses its nonce after seeing others.

### Procedure (session-typed API)

The implementation no longer exposes raw `signRound1/2`. Use the linear, session-typed API in `Protocol/Sign/Session.lean`:

```lean
open IceNine.Protocol.SignSession

-- caller supplies fresh randomness
let ready := initSession S keyShare msg session hidingNonce bindingNonce opening
match commit S ready with
| .error err => -- session reuse or commitment reuse detected locally
| .ok { committed, msg := commitMsg, tracker, nonceReg } =>
  -- after collecting commits and computing challenge/binding factors:
  let (revealed, revealMsg, tracker', nonceReg') :=
    reveal S committed challenge bindingFactor aggregateW tracker nonceReg
  match sign S revealed tracker' nonceReg' with
  | .inl (signed, tracker'', nonceReg'') => finalize S signed
  | .inr _      => -- retry with NEW FreshNonce via retryWithFreshNonce
```

Round‑1 message contents are identical: each `SignCommitMsg` carries the hash commitment plus both public nonce values.

Each party $P_i \in S$ still samples fresh $(y_{\text{hiding}}, y_{\text{binding}})$, computes
$W_{\text{hiding}} = A(y_{\text{hiding}})$, $W_{\text{binding}} = A(y_{\text{binding}})$,
samples an opening $\rho_i$, and broadcasts the commitment to $W_{\text{hiding}}$ together with both public nonces. The implementation also:
- marks the `session` as used in a per-party `SessionTracker`
- records `commitW` in a per-party `NonceRegistry` and rejects if the same commitment was used in a different session for that party.

### Commit Phase State

The commit phase accumulates commit messages in a semilattice structure.

```lean
structure CommitState (S : Scheme) :=
  (commits : List (DkgCommitMsg S))

instance (S : Scheme) : Join (CommitState S) :=
  ⟨fun a b => { commits := a.commits ⊔ b.commits }⟩
```

### Waiting for Commits

Each party waits until it receives commitments from all other parties in $S$. If a commitment does not arrive within a timeout the party may abort or exclude the missing party.

## Nonce Reveal and Challenge Computation

After all commitments are received parties reveal their nonces and compute the shared challenge.

### Reveal Phase

Each party $P_i$ broadcasts only the opening $\rho_i$ for its hiding commitment.
The public nonces (`hidingVal`, `bindingVal`) were already sent in Round 1 inside `SignCommitMsg`.
Trackers (`SessionTracker`, `NonceRegistry`) are threaded through; no additional updates occur in this phase.

### Verification

Each party verifies all received openings. For each $P_j \in S$ check that

$$\mathsf{Com}(w_j, \rho_j) = \mathsf{Com}^{(w)}_j$$

If any opening is invalid the party aborts the session. It may also file a complaint identifying the misbehaving party.

### Nonce Aggregation

After successful verification compute the aggregated nonce.

$$w = \sum_{i \in S} w_i$$

### Challenge Derivation

Compute the challenge using the hash function.

$$c = H(m, \mathsf{pk}, S, \{\mathsf{Com}^{(w)}_i\}_{i \in S}, w)$$

The challenge depends on the message, public key, signer set, all commitments, and the aggregated nonce. Including the commitments in the hash input binds the challenge to the commit phase.

## Round 2: Partial Signatures

In round two each party produces its partial signature.

### n-of-n Case

In the $n$-of-$n$ setting all parties must participate. The session transition `sign`
in `SignSession` computes each partial signature as

$$z_i = y_i + c \cdot s_i$$

This is the standard Schnorr response. The ephemeral secret masks the product of challenge and secret share. The function returns `none` if the norm check fails.

### t-of-n Case

In the $t$-of-$n$ setting a subset of parties signs. Each party must adjust its contribution using Lagrange coefficients.

```lean
structure LagrangeCoeff (S : Scheme) :=
  (pid    : S.PartyId)
  (lambda : S.Scalar)
```

Let $\lambda_i^S$ denote the Lagrange coefficient for party $i$ over the signing set $S$. Party $P_i$ computes

$$z_i = y_i + c \cdot \lambda_i^S \cdot s_i$$

The Lagrange coefficient ensures that the sum of adjusted shares equals the master secret.

### Lagrange Coefficient Computation

```lean
def lagrangeCoeffAtZero
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (pidToScalar : S.PartyId → S.Scalar)
  (Sset : List S.PartyId) (i : S.PartyId) : S.Scalar
```

The Lagrange coefficient for party $i$ over set $S$ is

$$\lambda_i^S = \prod_{j \in S, j \neq i} \frac{j}{j - i}$$

This computation uses party identifiers as evaluation points. All arithmetic is in the scalar ring $R$. Returns 0 if duplicate identifiers would cause division by zero.

### Norm Check

Before broadcasting the partial signature each party may check the norm.

$$\mathsf{normOK}(z_i)$$

If the norm exceeds the bound the party aborts this session. It can retry with a fresh nonce. This check prevents leakage through the response distribution.

### Broadcasting Partials

Each party $P_i$ broadcasts its partial signature $z_i$ to all parties in $S$.

## Aggregation

An aggregator collects all partial signatures and produces the final signature.

### Shares Phase State

The shares phase accumulates partial signatures along with threshold context. Messages are stored in `MsgMap` structures keyed by sender ID, making conflicting messages from the same sender un-expressable.

```lean
structure ShareState (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] :=
  (commits : CommitMap S)   -- at most one commit per party
  (reveals : RevealMap S)   -- at most one reveal per party
  (shares  : ShareMap S)    -- at most one share per party
  (active  : Finset S.PartyId)

structure ShareWithCtx (S : Scheme) :=
  (state : ShareState S)
  (ctx   : ThresholdCtx S)
```

The `MsgMap` structure provides conflict detection: `tryAddShare` returns a conflict indicator if a party attempts to submit multiple shares, enabling detection of Byzantine behavior.

The threshold context ensures aggregation only proceeds when sufficient parties contribute.

```lean
inductive SignMode | all | threshold

inductive CoeffStrategy (S : Scheme)
  | ones                                      -- n-of-n: z = Σ z_i
  | lagrange (coeffs : List (LagrangeCoeff S)) -- t-of-n: z = Σ λ_i·z_i

structure ThresholdCtx (S : Scheme) :=
  (active     : Finset S.PartyId)    -- participating signers
  (t          : Nat)                 -- threshold (t = |active| for n-of-n)
  (mode       : SignMode)            -- n-of-n vs t-of-n
  (strategy   : CoeffStrategy S)     -- aggregation method
  (card_ge    : t ≤ active.card)     -- proof: have enough signers
  (strategy_ok : strategyOK S active.toList strategy) -- coeffs align
```

The `CoeffStrategy` type selects the aggregation path:
- `ones`: simple sum z = Σ z_i (n-of-n, no field operations)
- `lagrange coeffs`: weighted sum z = Σ λ_i·z_i (t-of-n, requires field)

### Context Constructors

Smart constructors build `ThresholdCtx` with proofs:

```lean
-- n-of-n: threshold = |active|, strategy = ones
def mkAllCtx (S : Scheme) [DecidableEq S.PartyId]
  (active : Finset S.PartyId) : ThresholdCtx S

-- t-of-n with pre-supplied coefficients
def mkThresholdCtx
  (S : Scheme) [DecidableEq S.PartyId]
  (active : Finset S.PartyId)
  (t : Nat)
  (coeffs : List (LagrangeCoeff S))
  (hcard : t ≤ active.card)
  (halign : coeffs.map (·.pid) = active.toList)
  (hlen : coeffs.length = active.toList.length)
  : ThresholdCtx S

-- t-of-n with computed Lagrange coefficients (requires Field)
def mkThresholdCtxComputed
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (active : Finset S.PartyId)
  (t : Nat)
  (pidToScalar : S.PartyId → S.Scalar)
  (hcard : t ≤ active.card) : ThresholdCtx S
```

### Collecting Partials

The aggregator receives $z_i$ from each $P_i \in S$. If any partial is missing the aggregator may wait or abort.

### Signature Structure

```lean
structure Signature (S : Scheme) :=
  (z       : S.Secret)
  (c       : S.Challenge)
  (Sset    : List S.PartyId)
  (commits : List S.Commitment)
  (context : ExternalContext := {})  -- merged from contributing shares
```

The signature's context is merged from all contributing shares, enabling external protocols to verify consensus binding.

### Signature Computation

For n-of-n aggregation:

```lean
def aggregateSignature
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  : Signature S
```

Compute the aggregated response.

$$z = \sum_{i \in S} z_i$$

For t-of-n aggregation with Lagrange weighting:

```lean
def aggregateSignatureLagrange
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (coeffs : List (LagrangeCoeff S))
  (shares : List (SignShareMsg S))
  : Signature S
```

### Strategy-Based Aggregation

The `aggregateWithStrategy` function selects the aggregation path based on the coefficient strategy:

```lean
def aggregateWithStrategy
  (S    : Scheme) [DecidableEq S.PartyId]
  (c    : S.Challenge)
  (active : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  (strategy : CoeffStrategy S)
  : Option (Signature S)
```

This function validates that all shares come from the declared active set, then dispatches to `aggregateSignature` (for `.ones`) or `aggregateSignatureLagrange` (for `.lagrange coeffs`).

### Context-Based Aggregation

For full validation using the threshold context:

```lean
def aggregateSignatureWithCtx
  (S    : Scheme) [DecidableEq S.PartyId]
  (c    : S.Challenge)
  (ctx  : ThresholdCtx S)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  : Option (Signature S)
```

This function checks `sharesFromActive` (membership validation) before delegating to `aggregateWithStrategy` using the context's strategy.

### Final Signature

The signature consists of the following components.

$$\sigma = (z, c, S, \{\mathsf{Com}^{(w)}_i\}_{i \in S})$$

The signature includes the aggregated response, the challenge, the signer set, and all nonce commitments.

## Correctness

The aggregated response satisfies the verification equation. Consider the $n$-of-$n$ case.

$$z = \sum_{i \in S} z_i = \sum_{i \in S} (y_i + c \cdot s_i) = \sum_{i \in S} y_i + c \cdot \sum_{i \in S} s_i = y + c \cdot s$$

where $y = \sum_i y_i$ and $s = \sum_i s_i$.

Applying the linear map $A$ gives

$$A(z) = A(y) + c \cdot A(s) = w + c \cdot \mathsf{pk}$$

Rearranging yields

$$A(z) - c \cdot \mathsf{pk} = w$$

The verifier recomputes $w$ from this equation and checks the challenge.

### t-of-n Correctness

In the $t$-of-$n$ case the Lagrange coefficients ensure

$$\sum_{i \in S} \lambda_i^S \cdot s_i = s$$

The rest of the argument follows as above.

## Session Binding

The challenge binds to the specific session through several mechanisms.

1. The message $m$ is included in the hash input.
2. The public key $\mathsf{pk}$ is included.
3. The signer set $S$ is included.
4. All nonce commitments are included.
5. The aggregated nonce $w$ is included.

This binding prevents cross-session attacks where an adversary reuses partial signatures from different sessions.

## Transcript Validation

The `validateSigning` function checks the entire signing transcript before aggregation.
Its current signature also requires precomputed binding factors (derived from the commit list):

```lean
def validateSigning
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (bindingFactors : BindingFactors S)
  (shares  : List (SignShareMsg S))
  : Except (SignError S.PartyId) (Signature S)
```

Callers must compute `bindingFactors` (e.g., via `computeBindingFactors`) and supply them; otherwise validation will not type-check.

### Error Types

```lean
inductive SignError (PartyId : Type) where
  | lengthMismatch : SignError PartyId
  | participantMismatch : PartyId → SignError PartyId
  | duplicateParticipants : PartyId → SignError PartyId
  | commitMismatch : PartyId → SignError PartyId
  | sessionMismatch : Nat → Nat → SignError PartyId
```

Note: Legacy error variants (`normCheckFailed`, `maxRetriesExceeded`, `sessionAborted`) have been removed. With local rejection sampling, norm bounds are handled locally. Session-level aborts use `AbortReason` from `Protocol/Core/Abort.lean`.

### Valid Transcript Predicate

```lean
structure ValidSignTranscript (S : Scheme)
  (Sset : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S)) : Prop where
  len_comm_reveal : commits.length = reveals.length
  len_reveal_share : reveals.length = shares.length
  pids_nodup : (commits.map (·.sender)).Nodup
  pids_eq : commits.map (·.sender) = Sset
  commit_open_ok : List.Forall₂ (fun c r => c.sender = r.sender ∧ S.commit c.hiding r.opening = c.commitW) commits reveals
  sessions_ok : let sess := (commits.head?.map (·.session)).getD 0; ∀ sh ∈ shares, sh.session = sess
```

## Monotonic Step Functions

State transitions are monotone with respect to the semilattice order.

```lean
def stepCommit (S : Scheme) (msg : DkgCommitMsg S) (st : CommitState S) : CommitState S :=
  { commits := st.commits ⊔ [msg] }

lemma stepCommit_monotone (S : Scheme) (msg : DkgCommitMsg S) :
  ∀ a b, a ≤ b → stepCommit S msg a ≤ stepCommit S msg b
```

Similar monotonicity holds for `stepReveal` and `stepShare`.

## Abort Conditions

The signing protocol may abort under several conditions.

**Missing commitment.** A party in $S$ does not broadcast its commitment.

**Invalid opening.** A received opening does not match its commitment.

**Missing partial.** A party does not broadcast its partial signature.

**Norm violation.** A partial signature fails the norm check.

**Inconsistent challenge.** Parties compute different challenges due to inconsistent views.

**Session mismatch.** Messages have inconsistent session identifiers.

When aborting parties should discard all session state. They should not reuse the ephemeral nonce $y_i$ in any future session.

## Session Tracking and Nonce Safety

**CRITICAL**: Nonce reuse completely breaks Schnorr-style signatures.

If the same nonce $y$ is used with two different challenges $c_1, c_2$:
- $z_1 = y + c_1 \cdot sk$
- $z_2 = y + c_2 \cdot sk$

The secret key can be recovered: $sk = (z_1 - z_2) / (c_1 - c_2)$

This attack is formalized in `Proofs/Soundness/Soundness.lean` as the `nonce_reuse_key_recovery` theorem. See [Verification: Special Soundness](04_verification.md#special-soundness) for the formal proof.

### Session Tracker

Each party tracks used session IDs:

```lean
structure SessionTracker (S : Scheme) where
  usedSessions : Finset Nat    -- sessions that have been used
  partyId : S.PartyId

def SessionTracker.isFresh (tracker : SessionTracker S) (session : Nat) : Bool :=
  session ∉ tracker.usedSessions

def SessionTracker.markUsed (tracker : SessionTracker S) (session : Nat) : SessionTracker S :=
  { tracker with usedSessions := tracker.usedSessions.insert session }
```

### Session Validation

```lean
inductive SessionCheckResult
  | ok                           -- session is fresh
  | alreadyUsed (session : Nat)  -- DANGER: would reuse nonce
  | invalidId

def checkSession (tracker : SessionTracker S) (session : Nat) : SessionCheckResult :=
  if tracker.isFresh session then .ok
  else .alreadyUsed session
```

### Nonce Registry

For network-wide detection, the `NonceRegistry` uses HashMap-based indices for O(1) lookup:

```lean
structure NonceRegistry (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment] where
  bySession : Std.HashMap (S.PartyId × Nat) S.Commitment      -- primary index
  byCommitment : Std.HashMap (S.PartyId × S.Commitment) (List Nat)  -- reverse index

def NonceRegistry.hasCommitment (reg : NonceRegistry S)
    (pid : S.PartyId) (session : Nat) (commit : S.Commitment) : Bool :=
  match reg.bySession.get? (pid, session) with
  | some c => c == commit
  | none => false

def NonceRegistry.detectReuse (reg : NonceRegistry S)
    (pid : S.PartyId) (commit : S.Commitment) : Option (Nat × Nat) :=
  match reg.byCommitment.get? (pid, commit) with
  | some (s1 :: s2 :: _) => if s1 ≠ s2 then some (s1, s2) else none
  | _ => none
```

The dual index structure provides:
- **O(1) lookup** by (partyId, session) for commitment retrieval
- **O(1) reuse detection** by (partyId, commitment) for security monitoring

## Local Rejection Sampling

In lattice signatures, the response $z$ must have bounded norm to prevent leakage. Ice Nine uses **local rejection sampling** where each signer independently ensures their partial signature satisfies norm bounds before broadcasting.

### Key Invariant

If each of $T$ signers produces $z_i$ with $\|z_i\|_\infty \leq B_{\text{local}}$, then the aggregate $z = \sum z_i$ satisfies $\|z\|_\infty \leq T \cdot B_{\text{local}} \leq B_{\text{global}}$.

This eliminates global rejection as a distributed control-flow path.

### Local Sign Result

```lean
inductive LocalSignResult (S : Scheme)
  | success (z_i : S.Secret) (hidingNonce bindingNonce : S.Secret) (attempts : Nat)
  | failure (err : LocalRejectionError S.PartyId)
```

### Rejection Loop

Each signer runs local rejection sampling independently:

```lean
def localRejectionLoop (S : Scheme) (cfg : ThresholdConfig)
    (partyId : S.PartyId) (sk_i : S.Secret) (challenge : S.Challenge)
    (bindingFactor : S.Scalar) (sampleNonce : IO (S.Secret × S.Secret))
    : IO (LocalSignResult S)
```

The loop:
1. Samples fresh nonce pair $(y_{\text{hiding}}, y_{\text{binding}})$
2. Computes $z_i = y_{\text{hiding}} + \rho \cdot y_{\text{binding}} + c \cdot sk_i$
3. Checks if $\|z_i\|_\infty \leq B_{\text{local}}$
4. Returns success or retries with new nonces (up to `maxLocalAttempts`)

### Parallelization

Local rejection is trivially parallelizable:
- **Across signers**: Each signer's loop is independent
- **Within signer**: Batch multiple nonce candidates (`localRejectionLoopParallel`)
- **Within batch**: SIMD/vectorized norm checking

**Reference**: Lyubashevsky, "Fiat-Shamir with Aborts", ASIACRYPT 2009.

## Session Abort Coordination

While local rejection handles norm bounds, session-level aborts are needed for:
- **Liveness failures**: Parties offline, session times out
- **Security violations**: Trust assumption violated (more than $n-t$ faulty parties)
- **Explicit cancellation**: Group decides to abandon signing

### Abort Reasons

```lean
inductive AbortReason (PartyId : Type*) where
  -- Liveness failures (require f+1 votes)
  | timeout (respondents : Nat) (required : Nat)
  | insufficientParticipants (actual : Nat) (required : Nat)
  | partyUnresponsive (parties : List PartyId)

  -- Security violations (immediate abort, no voting)
  | trustViolation (faultyCount : Nat) (maxTolerable : Nat)
  | globalNormExceeded (aggregateNorm : Nat) (bound : Nat)
  | tooManyComplaints (complaints : Nat) (maxTolerable : Nat)

  -- Explicit request (requires f+1 votes)
  | requestedBy (requester : PartyId)
```

### Abort State (CRDT)

```lean
structure AbortState (S : Scheme) where
  session : Nat
  votes : Finset S.PartyId
  reasons : List (AbortReason S.PartyId)
  immediateTriggered : Bool := false

instance (S : Scheme) : Join (AbortState S) :=
  ⟨fun a b => {
    session := a.session
    votes := a.votes ∪ b.votes
    reasons := (a.reasons ++ b.reasons).dedup
    immediateTriggered := a.immediateTriggered || b.immediateTriggered
  }⟩
```

### Abort Threshold

Abort consensus uses `ThresholdConfig.abortThreshold` which is $f + 1$ where $f = n - t$ (max faulty parties). This ensures at least one honest party agreed to abort, preventing malicious minorities from forcing spurious aborts.

```lean
def ThresholdConfig.abortThreshold (cfg : ThresholdConfig) : Nat :=
  cfg.maxFaulty + 1

def AbortState.shouldAbort (state : AbortState S) (cfg : ThresholdConfig) : Bool :=
  state.hasImmediateReason || state.isConfirmedByVotes cfg
```

Security violations trigger immediate abort without voting.

## Session-Typed Signing

The `Protocol/Sign/Session.lean` module provides a session-typed API that makes nonce reuse a compile-time error rather than a runtime check. Each signing session progresses through states that consume the previous state, ensuring nonces are used exactly once.

### Session State Machine

```
ReadyToCommit ──► Committed ──► Revealed ──► SignedWithStats ──► Done
                      │              │
                      └──────► Aborted ◄──────┘
```

Each transition consumes its input state. There is no way to "go back" or reuse a consumed state. The `ReadyToCommit` state contains a `FreshNonce` that gets consumed during the commit transition. Sessions may transition to `Aborted` from `Committed` or `Revealed` when abort consensus is reached.

### Linear Nonce (Dual Nonce Version)

Following FROST, we use two nonces per signer:

```lean
structure FreshNonce (S : Scheme) where
  private mk ::
  private hidingNonce : S.Secret    -- secret hiding nonce
  private bindingNonce : S.Secret   -- secret binding nonce
  private publicHiding : S.Public   -- W_hiding = A(hiding)
  private publicBinding : S.Public  -- W_binding = A(binding)
  private opening : S.Opening       -- commitment opening

def FreshNonce.sample (S : Scheme) (h b : S.Secret) (opening : S.Opening) : FreshNonce S
```

The private constructor prevents arbitrary creation. The only way to create a `FreshNonce` is via `sample` with fresh randomness for both hiding and binding nonces.

### Session States

Each state carries the data accumulated up to that point (dual nonce version):

```lean
structure ReadyToCommit (S : Scheme) where
  keyShare : KeyShare S
  nonce : FreshNonce S      -- dual nonces, will be consumed on commit
  message : S.Message
  session : Nat

structure Committed (S : Scheme) where
  keyShare : KeyShare S
  private hidingNonce : S.Secret   -- moved from FreshNonce
  private bindingNonce : S.Secret  -- moved from FreshNonce
  publicHiding : S.Public
  publicBinding : S.Public
  opening : S.Opening
  message : S.Message
  session : Nat
  commitment : S.Commitment
  nonceConsumed : NonceConsumed S  -- proof token

structure Revealed (S : Scheme) where
  keyShare : KeyShare S
  private hidingNonce : S.Secret
  private bindingNonce : S.Secret
  publicHiding : S.Public
  publicBinding : S.Public
  message : S.Message
  session : Nat
  challenge : S.Challenge
  bindingFactor : S.Scalar     -- ρ for this signer
  aggregateNonce : S.Public    -- w = Σ (W_hiding_i + ρ_i·W_binding_i)

structure SignedWithStats (S : Scheme) extends Signed S where
  localAttempts : Nat      -- number of local rejection attempts
  hidingNonce : S.Secret   -- the nonce used
  bindingNonce : S.Secret

structure Done (S : Scheme) where
  shareMsg : SignShareMsg S

structure Aborted (S : Scheme) where
  session : Nat
  reason : AbortReason S.PartyId
  voteCount : Nat
```

### Session Transitions

Each transition function consumes its input and produces the next state:

```lean
-- Consumes ReadyToCommit, produces Committed
-- The FreshNonce inside is consumed; cannot be accessed again
def commit (S : Scheme) (ready : ReadyToCommit S)
    : Except (SignError S.PartyId) (CommitResult S)

-- Consumes Committed, produces Revealed
-- Receives challenge, binding factor, and aggregate nonce from coordinator
def reveal (S : Scheme) (committed : Committed S)
    (challenge : S.Challenge) (bindingFactor : S.Scalar) (aggregateW : S.Public)
    : Revealed S × SignRevealWMsg S × SessionTracker S × NonceRegistry S

-- Consumes Revealed, produces SignedWithStats using local rejection sampling
-- Never fails norm check because rejection happens internally
def signWithLocalRejection (S : Scheme) (revealed : Revealed S)
    (cfg : ThresholdConfig) (sampleNonce : IO (S.Secret × S.Secret))
    : IO (Except (LocalRejectionError S.PartyId) (SignedWithStats S))

-- Consumes Signed, produces Done
def finalize (S : Scheme) (signed : Signed S) : Done S

-- Abort transitions (consume current state, produce Aborted)
def abortFromCommitted (S : Scheme) (committed : Committed S)
    (reason : AbortReason S.PartyId) (voteCount : Nat) : Aborted S

def abortFromRevealed (S : Scheme) (revealed : Revealed S)
    (reason : AbortReason S.PartyId) (voteCount : Nat) : Aborted S
```

### Local Rejection vs Global Abort

With local rejection sampling, norm bounds are handled **locally** by each signer:
- Each signer runs rejection sampling independently
- No global retry coordination needed
- `signWithLocalRejection` never returns a norm failure

Session aborts are for **global** failures that cannot be resolved locally:
- Timeout waiting for other parties
- Security violations (trust assumption breached)
- Explicit cancellation by consensus

### Type-Level Guarantees

The session type system provides these guarantees:

1. **Nonce uniqueness**: Each `FreshNonce` can only be consumed once. The `commit` function consumes the `ReadyToCommit` state, and the nonce value moves into `Committed`. There's no path back.

2. **Linear flow**: States can only progress forward. Each transition consumes its input. Sessions may also transition to `Aborted`.

3. **Local rejection**: With `signWithLocalRejection`, norm bounds are satisfied during signing via local rejection sampling. No global retry loop is needed.

4. **Compile-time enforcement**: These aren't runtime checks—the type system prevents writing code that would reuse a nonce.

5. **Abort safety**: Aborted sessions cannot continue. Once a session transitions to `Aborted`, any consumed nonces are invalidated.

### Example: Nonce Reuse is Uncompilable

```lean
-- This CANNOT compile because `ready` is consumed by first `commit`
def badNonceReuse (S : Scheme) (ready : ReadyToCommit S) :=
  let (committed1, _) := commit S ready  -- consumes ready
  let (committed2, _) := commit S ready  -- ERROR: ready already consumed
  (committed1, committed2)
```

## Fast-Path Signing

For latency-sensitive applications, Ice Nine supports single-round signing when nonces are precomputed and pre-shared. This mode skips the commit-reveal round by preparing nonces during idle time.

### Precomputed Nonces

```lean
structure PrecomputedNonce (S : Scheme) where
  commitment : S.Commitment
  nonce : FreshNonce S
  publicHiding : S.Public
  publicBinding : S.Public
  generatedAt : Nat
  maxAge : Nat := 3600  -- 1 hour default expiry

structure NoncePool (S : Scheme) where
  available : List (PrecomputedNonce S)
  consumedCount : Nat := 0
```

### Fast Signing Function

```lean
def signFast (S : Scheme)
    (keyShare : KeyShare S)
    (precomputed : PrecomputedNonce S)
    (challenge : S.Challenge)
    (bindingFactor : S.Scalar)
    (session : Nat)
    (context : ExternalContext := {})
    : Option (SignShareMsg S)
```

This function produces a signature share immediately using a precomputed nonce. It SHOULD return `none` if the norm check fails, requiring a fresh nonce. **Implementation note:** the current Lean code stubs out the norm check and always returns `some`; production code must call `S.normOK` here and propagate failure.

### Security Assumptions

Fast-path signing trusts that:
1. Nonce commitments were honestly generated
2. Nonces are not being reused (enforced by `FreshNonce` type)
3. Precomputed nonces have not expired
4. The coordinator will aggregate honestly

Use standard two-round signing when these assumptions don't hold.

See [Protocol Integration](06_integration.md) for detailed usage patterns with external consensus protocols.

## Security Considerations

**Nonce reuse.** Using the same nonce $y_i$ in two sessions leaks the secret share $s_i$. Session types make nonce reuse a compile-time error.

**Commitment binding.** The commitment prevents a party from choosing its nonce adaptively. This protects against rogue key attacks.

**Challenge entropy.** The hash function must produce challenges with sufficient entropy. In the random oracle model this is guaranteed.

**Norm bounds.** The norm check prevents statistical leakage of the secret through the response distribution. Local rejection sampling ensures each partial signature is independent of the secret—no global retry coordination needed.

**Abort coordination.** Session-level aborts (for liveness failures or security violations) use CRDT state with an $f+1$ threshold, ensuring at least one honest party agreed to abort.

**Totality.** The validation function always returns either a valid signature or a structured error.
