/-
# Threshold Signing Protocol

Two-round threshold signing following the Schnorr pattern:
  Round 1: Parties commit to ephemeral nonces
  Round 2: Parties reveal nonces, compute challenge, produce partial signatures
  Aggregation: Combine partials into final signature

Supports both n-of-n (all parties) and t-of-n (threshold) signing.
Security proofs in `Security/Sign`.

## API

**Use the session-typed API from `IceNine.Protocol.SignSession`.**

The session-typed API provides compile-time guarantees against nonce reuse:
- Each `FreshNonce` can only be consumed once
- Session states progress linearly: ReadyToCommit → Committed → Revealed → Signed → Done
- Retry handling requires a NEW fresh nonce

Example:
```lean
import IceNine.Protocol.SignSession
open IceNine.Protocol.SignSession

-- Initialize with fresh nonce
let ready := initSession S keyShare message sessionId y opening
-- Commit (consumes ready, produces committed)
let (committed, commitMsg) := commit S ready
-- ... receive all commits, compute challenge ...
-- Reveal (consumes committed)
let (revealed, revealMsg) := reveal S committed challenge aggregateW
-- Sign (consumes revealed)
match sign S revealed with
| Sum.inl signed => finalize S signed
| Sum.inr (_, reason) => -- retry with FRESH nonce
```

This module provides supporting types, validation, and aggregation functions.
The raw `signRound1` and `signRound2` functions have been removed to prevent
accidental nonce misuse.
-/

import IceNine.Protocol.Core
import IceNine.Protocol.Phase  -- for Join class
import Mathlib

namespace IceNine.Protocol

open List

/-!
## State and Message Types

Each signing session has a unique session ID. Parties maintain local state
with their ephemeral nonce and exchange commit/reveal/share messages.
-/

/-!
## Session and Nonce Safety

**CRITICAL**: Nonce reuse is catastrophic for Schnorr-style signatures.
If the same nonce y is used with two different challenges c₁, c₂:
  z₁ = y + c₁·sk
  z₂ = y + c₂·sk
Then: sk = (z₁ - z₂) / (c₁ - c₂)  -- secret key recovered!

We track used sessions to prevent this attack vector.

### Session ID Generation

Session IDs must be unique across all signing sessions for a given party.
Recommended strategies (in order of preference):

1. **Cryptographic random**: Generate 128+ bit random session ID using CSPRNG.
   Collision probability negligible. Best for distributed systems.

2. **Monotonic counter + party ID**: `(partyId, counter)` tuple where counter
   increments locally. Requires persistent storage but deterministic.

3. **Timestamp + random**: `(timestamp_ns, random_64bit)`. Good balance of
   uniqueness and debuggability.

**WARNING**: Do NOT use:
- Sequential counters without party ID (collisions across parties)
- Predictable values (may enable targeted attacks)
- Message hash alone (same message = same session = nonce reuse!)

The `SessionTracker` below provides runtime detection of session reuse,
but proper generation is the primary defense.
-/

/-- Tracks used session IDs to prevent nonce reuse.
    Each party maintains this state across signing sessions. -/
structure SessionTracker (S : Scheme) where
  /-- Set of session IDs that have been used -/
  usedSessions : Finset Nat
  /-- Party ID this tracker belongs to -/
  partyId : S.PartyId
deriving Repr

/-- Check if a session ID is fresh (not previously used) -/
def SessionTracker.isFresh (tracker : SessionTracker S) (session : Nat) : Bool :=
  session ∉ tracker.usedSessions

/-- Mark a session as used (call after committing to nonce) -/
def SessionTracker.markUsed (tracker : SessionTracker S) (session : Nat)
    : SessionTracker S :=
  { tracker with usedSessions := tracker.usedSessions.insert session }

/-- Create empty tracker for a party -/
def SessionTracker.empty (S : Scheme) (pid : S.PartyId) : SessionTracker S :=
  { usedSessions := ∅, partyId := pid }

/-- Session validation result -/
inductive SessionCheckResult
  | ok                           -- session is fresh, safe to proceed
  | alreadyUsed (session : Nat)  -- DANGER: session was used before
  | invalidId                    -- session ID is malformed
deriving DecidableEq, Repr

/-- Validate session before starting signing -/
def checkSession (tracker : SessionTracker S) (session : Nat)
    : SessionCheckResult :=
  if tracker.isFresh session then .ok
  else .alreadyUsed session

/-- Nonce registry for detecting reuse across the network.
    This is a global view; in practice, parties only see their own history.

    **Implementation**: Uses HashMap for O(1) lookup by (partyId, session).
    Also maintains a reverse index from commitment to sessions for reuse detection. -/
structure NonceRegistry (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment] where
  /-- Primary index: (partyId, session) → commitment -/
  bySession : Std.HashMap (S.PartyId × Nat) S.Commitment
  /-- Reverse index: (partyId, commitment) → list of sessions (for reuse detection) -/
  byCommitment : Std.HashMap (S.PartyId × S.Commitment) (List Nat)
deriving Repr

/-- Empty nonce registry. -/
def NonceRegistry.empty (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    : NonceRegistry S :=
  { bySession := Std.HashMap.empty
    byCommitment := Std.HashMap.empty }

/-- Check if a nonce commitment was seen before (O(1) lookup). -/
def NonceRegistry.hasCommitment
    (reg : NonceRegistry S)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (pid : S.PartyId) (session : Nat) (commit : S.Commitment) : Bool :=
  match reg.bySession.get? (pid, session) with
  | some c => c == commit
  | none => false

/-- Check if a (party, session) pair exists (regardless of commitment). -/
def NonceRegistry.hasSession
    (reg : NonceRegistry S)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (pid : S.PartyId) (session : Nat) : Bool :=
  reg.bySession.contains (pid, session)

/-- Record a nonce commitment.
    Updates both indices. -/
def NonceRegistry.record
    (reg : NonceRegistry S)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (pid : S.PartyId) (session : Nat) (commit : S.Commitment) : NonceRegistry S :=
  let newBySession := reg.bySession.insert (pid, session) commit
  let key := (pid, commit)
  let sessions := reg.byCommitment.get? key |>.getD []
  let newByCommitment := reg.byCommitment.insert key (session :: sessions)
  { bySession := newBySession
    byCommitment := newByCommitment }

/-- Detect if same nonce was used in different sessions (attack detection).
    O(1) lookup using reverse index. Returns the two session IDs if reuse detected. -/
def NonceRegistry.detectReuse
    (reg : NonceRegistry S)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (pid : S.PartyId) (commit : S.Commitment) : Option (Nat × Nat) :=
  match reg.byCommitment.get? (pid, commit) with
  | some (s1 :: s2 :: _) => if s1 ≠ s2 then some (s1, s2) else none
  | _ => none

/-- Get all commitments as a list (for backward compatibility). -/
def NonceRegistry.toList
    (reg : NonceRegistry S)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    : List (S.PartyId × Nat × S.Commitment) :=
  reg.bySession.toList.map fun ((pid, session), commit) => (pid, session, commit)

/-!
## State and Message Types

Each signing session has a unique session ID. Parties maintain local state
with their ephemeral nonce and exchange commit/reveal/share messages.
-/

/-- Party's local state during signing. Contains ephemeral nonce y_i
    (sampled fresh each session) and commitment data. -/
structure SignLocalState (S : Scheme) where
  share   : KeyShare S   -- party's long-term credential from DKG
  msg     : S.Message    -- message being signed
  session : Nat          -- unique session identifier
  y_i     : S.Secret     -- ephemeral nonce (NEVER reuse across sessions!)
  w_i     : S.Public     -- public nonce = A(y_i)
  openW   : S.Opening    -- commitment randomness
deriving Repr

/-- Round 1 message: commitment to ephemeral nonce w_i.
    Hiding w_i until all commit prevents adaptive attacks. -/
structure SignCommitMsg (S : Scheme) where
  sender  : S.PartyId
  session : Nat
  commitW : S.Commitment
deriving Repr

/-- Reveal message: party discloses w_i and opening after all commits received.
    Others verify: commit(w_i, opening) = commitW from round 1. -/
structure SignRevealWMsg (S : Scheme) where
  sender  : S.PartyId
  session : Nat
  w_i     : S.Public
  opening : S.Opening
deriving Repr

/-- Lagrange coefficient for party i over signer set S.
    In t-of-n signing, partials are weighted: z = Σ λ_i·z_i. -/
structure LagrangeCoeff (S : Scheme) where
  pid    : S.PartyId
  lambda : S.Scalar     -- λ_i = Π_{j≠i} j/(j-i)
deriving Repr

/-!
## Error Handling

Structured errors identify exactly what went wrong during signing.
Includes abort conditions from rejection sampling failures.
-/

/-- Signing failure modes with identifying information. -/
inductive SignError (PartyId : Type u) where
  | lengthMismatch : SignError PartyId                 -- message count mismatch
  | participantMismatch : PartyId → SignError PartyId  -- unexpected party
  | duplicateParticipants : SignError PartyId          -- same party twice
  | commitMismatch : PartyId → SignError PartyId       -- reveal doesn't match commit
  | sessionMismatch : Nat → Nat → SignError PartyId    -- wrong session ID
  | normCheckFailed : PartyId → SignError PartyId      -- party's z_i failed norm bound
  | maxRetriesExceeded : PartyId → SignError PartyId   -- party exceeded retry limit
  | sessionAborted : Nat → SignError PartyId           -- session was aborted
  deriving DecidableEq

/-- Abort reason for detailed error reporting -/
inductive AbortReason (PartyId : Type u) where
  | normBoundExceeded : PartyId → Nat → AbortReason PartyId  -- party, attempt count
  | maxRetriesReached : PartyId → AbortReason PartyId
  | coordinationFailure : AbortReason PartyId                -- parties disagreed on retry
  | timeout : AbortReason PartyId
  deriving DecidableEq, Repr

/-- Session abort notification broadcast to all parties -/
structure SignAbortMsg (S : Scheme) where
  sender  : S.PartyId
  session : Nat
  reason  : AbortReason S.PartyId
deriving Repr

/-- Abort state tracked in CRDT for distributed coordination.
    Uses Finset for votes to ensure deduplication (each party gets one vote). -/
structure SignAbortState (S : Scheme) where
  /-- Session that was aborted (if any) -/
  abortedSession : Option Nat
  /-- Parties that requested abort (deduplicated) -/
  abortVotes : Finset S.PartyId
  /-- Abort reasons from each party (kept for debugging) -/
  reasons : List (S.PartyId × AbortReason S.PartyId)
deriving Repr

/-- CRDT merge for abort state: union votes (Finset union is commutative) -/
instance (S : Scheme) : Join (SignAbortState S) :=
  ⟨fun a b => {
    abortedSession := a.abortedSession <|> b.abortedSession
    abortVotes := a.abortVotes ∪ b.abortVotes
    reasons := a.reasons ++ b.reasons  -- reasons are for debugging, not consensus
  }⟩

/-- Empty abort state (no abort in progress) -/
def SignAbortState.empty (S : Scheme) : SignAbortState S :=
  { abortedSession := none, abortVotes := ∅, reasons := [] }

/-- Create abort state from a single abort message -/
def SignAbortState.fromMsg (S : Scheme) (msg : SignAbortMsg S) : SignAbortState S :=
  { abortedSession := some msg.session
    abortVotes := {msg.sender}
    reasons := [(msg.sender, msg.reason)] }

/-- Minimum abort threshold to prevent griefing.
    Requires majority: at least ⌈(n+1)/2⌉ parties must vote to abort.
    This prevents a single malicious party from causing repeated aborts. -/
def minAbortThreshold (totalParties : Nat) : Nat :=
  (totalParties + 1) / 2 + 1  -- Strictly more than half

/-- Check if session should be considered aborted.
    Requires at least `threshold` parties to agree, with a minimum of
    majority to prevent single-party griefing attacks.

    **Security Note**: The threshold should be set to at least `minAbortThreshold n`
    where n is the total number of parties. Using a lower threshold allows
    griefing attacks where a minority of parties can force repeated aborts. -/
def SignAbortState.isAborted (state : SignAbortState S) (threshold : Nat) (totalParties : Nat) : Bool :=
  let effectiveThreshold := max threshold (minAbortThreshold totalParties)
  state.abortVotes.card ≥ effectiveThreshold

/-- Safe abort check that automatically uses minimum threshold. -/
def SignAbortState.isSafelyAborted (state : SignAbortState S) (totalParties : Nat) : Bool :=
  state.abortVotes.card ≥ minAbortThreshold totalParties

/-- Create abort message when norm check fails -/
def mkNormAbortMsg (S : Scheme) (pid : S.PartyId) (session : Nat) (attempt : Nat)
    : SignAbortMsg S :=
  { sender := pid
    session := session
    reason := .normBoundExceeded pid attempt }

/-- Create abort message when max retries exceeded -/
def mkMaxRetryAbortMsg (S : Scheme) (pid : S.PartyId) (session : Nat)
    : SignAbortMsg S :=
  { sender := pid
    session := session
    reason := .maxRetriesReached pid }

/-- Predicate capturing a valid signing transcript.
    All messages consistent, commitments verified, sessions match. -/
structure ValidSignTranscript (S : Scheme)
  (Sset : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S)) : Prop where
  len_comm_reveal : commits.length = reveals.length
  len_reveal_share : reveals.length = shares.length
  pids_nodup : (commits.map (·.sender)).Nodup
  pids_eq : commits.map (·.sender) = Sset
  commit_open_ok :
    List.Forall₂ (fun c r => c.sender = r.sender ∧ S.commit r.w_i r.opening = c.commitW) commits reveals
  sessions_ok :
    let sess := (commits.head?.map (·.session)).getD 0;
    ∀ sh ∈ shares, sh.session = sess

/-!
## Lagrange Interpolation

For t-of-n threshold signing, partial signatures are weighted by
Lagrange coefficients to reconstruct the full signature.
-/

/-- Compute Lagrange coefficient λ_i for party i evaluating at 0.
    λ_i = Π_{j∈S, j≠i} x_j / (x_j - x_i) where x_k = pidToScalar(k). -/
def lagrangeCoeffAtZero
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId] [DecidableEq S.Scalar]
  (pidToScalar : S.PartyId → S.Scalar)
  (Sset : List S.PartyId) (i : S.PartyId) : S.Scalar :=
  let xi := pidToScalar i
  let others := Sset.erase i
  -- Return 0 if duplicate scalar values (would cause division by zero)
  if hdup : (others.any (fun j => decide (pidToScalar j = xi))) then 0 else
    (others.map (fun j => let xj := pidToScalar j; xj / (xj - xi))).prod

/-- Compute all Lagrange coefficients for a signer set. -/
def lagrangeCoeffs
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId] [DecidableEq S.Scalar]
  (pidToScalar : S.PartyId → S.Scalar)
  (Sset : List S.PartyId) : List (LagrangeCoeff S) :=
  Sset.map (fun pid => { pid := pid, lambda := lagrangeCoeffAtZero S pidToScalar Sset pid })

/-!
## Round 1: Nonce Commitment

**Use the session-typed API from `IceNine.Protocol.SignSession`** which provides
compile-time guarantees against nonce reuse. The raw round functions have been
removed to prevent accidental misuse.

Party samples ephemeral nonce y_i, computes w_i = A(y_i), commits to w_i.
The commitment hides w_i until all parties have committed.
-/

/-!
## Challenge Derivation

After all reveals, compute aggregate nonce w = Σ w_i and derive
challenge c = H(m, pk, S, commits, w) via Fiat-Shamir.
-/

/-- Compute Fiat-Shamir challenge from transcript.
    Returns (challenge, aggregate_nonce). -/
def computeChallenge
  (S     : Scheme)
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  : Option (S.Challenge × S.Public) :=
  -- Aggregate nonces: w = Σ w_i
  let w : S.Public := (reveals.map (·.w_i)).sum
  -- Hash full transcript to derive challenge
  let c : S.Challenge := S.hash m pk Sset (commits.map (fun cmsg => cmsg.commitW)) w
  some (c, w)

/-!
## Round 2: Partial Signature

**Use the session-typed API from `IceNine.Protocol.SignSession`** which provides
compile-time guarantees against nonce reuse. The raw round functions have been
removed to prevent accidental misuse.

Party computes z_i = y_i + c·sk_i. The ephemeral nonce y_i masks the
secret share so z_i reveals nothing about sk_i alone.

### Rejection Sampling

In lattice signatures, the response z must have bounded norm to prevent
leakage. If ||z|| is too large, the party must:
1. Sample a fresh nonce y'
2. Recompute w' = A(y') and get new challenge c' = H(m, pk, w')
3. Try again with z' = y' + c'·s

This requires coordination - all parties must restart together.
Expected attempts: ~4 for Dilithium parameters.

**Reference**: Lyubashevsky, "Fiat-Shamir with Aborts", ASIACRYPT 2009.
-/

/-- Maximum retry attempts before declaring abort.
    Dilithium expects ~4 attempts; we allow more for safety margin. -/
def maxSigningAttempts : Nat := 16

/-- Signing attempt outcome -/
inductive SignAttemptResult (S : Scheme)
  | success (msg : SignShareMsg S)  -- z_i passed norm check
  | retry                           -- need fresh nonce, try again
  | abort                           -- max attempts exceeded
deriving Repr

/-!
## Signature Aggregation

Combine partial signatures into final signature.
- n-of-n: simple sum z = Σ z_i
- t-of-n: weighted sum z = Σ λ_i·z_i via Lagrange
-/

/-- Final signature: z, challenge c, signer set, commitments. -/
structure Signature (S : Scheme) where
  z       : S.Secret           -- aggregated signature value
  c       : S.Challenge        -- Fiat-Shamir challenge
  Sset    : List S.PartyId     -- signers who participated
  commits : List S.Commitment  -- commitments (for verification)

/-!
## Aggregation Strategies

We unify n-of-n and t-of-n aggregation under a single strategy abstraction.
When the coefficients are all 1 (the all-parties case), we take the cheap
additive path with no inverses. When supplied with Lagrange coefficients, we
take the weighted path. Validation makes sure coefficients align with the
active set and share list to avoid misuse.
-/

/-- Simple n-of-n aggregation: z = Σ z_i. -/
def aggregateSignature
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  : Signature S :=
  let z : S.Secret := (shares.map (·.z_i)).sum
  { z := z, c := c, Sset := Sset, commits := commits }

/-- Weighted aggregation: z = Σ λ_i·z_i via provided coefficients. -/
def aggregateSignatureLagrange
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (coeffs : List (LagrangeCoeff S))
  (shares : List (SignShareMsg S))
  : Signature S :=
  let z : S.Secret :=
    (List.zipWith (fun coeff sh => coeff.lambda • sh.z_i) coeffs shares).sum
  { z := z, c := c, Sset := Sset, commits := commits }

/-!
### Unified Strategy

CoeffStrategy selects how partials are combined:
- ones: simple sum z = Σ z_i (n-of-n, no field ops needed)
- lagrange: weighted sum z = Σ λ_i·z_i (t-of-n, requires field)
-/

/-- Coefficient strategy: how to combine partial signatures. -/
inductive CoeffStrategy (S : Scheme)
  | ones                                      -- n-of-n: z = Σ z_i
  | lagrange (coeffs : List (LagrangeCoeff S)) -- t-of-n: z = Σ λ_i·z_i

/-- Validity predicate: coefficients align with active signer list.
    Prevents length/ordering mismatches during zipWith. -/
def strategyOK (S : Scheme) [DecidableEq S.PartyId]
  (active : List S.PartyId) : CoeffStrategy S → Prop
  | .ones => True
  | .lagrange coeffs =>
      coeffs.length = active.length ∧ coeffs.map (·.pid) = active

/-- Aggregate using strategy, validating shares against active set.
    Returns none on membership or length failures. -/
def aggregateWithStrategy
  (S    : Scheme) [DecidableEq S.PartyId]
  (c    : S.Challenge)
  (active : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  (strategy : CoeffStrategy S)
  : Option (Signature S) :=
  -- Membership check: all shares from declared active set
  if hfrom : ∀ sh ∈ shares, sh.sender ∈ active then
    match strategy with
    | .ones =>
        -- n-of-n path: just need length match
        if hlen : shares.length = active.length then
          some (aggregateSignature S c active commits shares)
        else none
    | .lagrange coeffs =>
        -- t-of-n path: coeffs must align with shares
        if hlen : shares.length = coeffs.length then
          if hpid : coeffs.map (·.pid) = active then
            some (aggregateSignatureLagrange S c active commits coeffs shares)
          else none
        else none
  else none

/-!
## Transcript Validation

Full validation of signing transcript before aggregation.
Checks lengths, sessions, commitments, and participants.
-/

/-- Validate transcript and produce signature if valid.
    Returns specific error on failure for debugging. -/
def validateSigning
  (S     : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment]
  [Decidable (∀ (r : SignRevealWMsg S) (c : SignCommitMsg S), S.commit r.w_i r.opening = c.commitW)]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  : Except (SignError S.PartyId) (Signature S) := do
  -- Check message counts match
  if commits.length = reveals.length ∧ reveals.length = shares.length then pure () else
    throw .lengthMismatch
  let sess := (commits.head?.map (·.session)).getD 0
  let pids := commits.map (·.sender)
  -- Check no duplicate signers
  if pids.Nodup then pure () else
    -- Find first duplicate: safe to use head since non-Nodup implies non-empty
    let firstPid := pids.head!
    throw (.duplicateParticipants firstPid)
  -- Check signers match expected set
  if pids = Sset then pure () else
    -- Find first mismatched party
    let mismatch := pids.find? (· ∉ Sset) |>.orElse (fun _ => Sset.find? (· ∉ pids))
    match mismatch with
    | some pid => throw (.participantMismatch pid)
    | none => throw .lengthMismatch  -- shouldn't happen if pids ≠ Sset
  -- Verify each commitment opens correctly
  for (c,r) in List.zip commits reveals do
    if c.sender = r.sender then
      if decide (S.commit r.w_i r.opening = c.commitW) then
        if r.session = sess then pure ()
        else throw (.sessionMismatch sess r.session)
      else throw (.commitMismatch r.sender)
    else throw (.participantMismatch c.sender)
  -- Check all shares have same session
  for sh in shares do
    if sh.session = sess then pure () else throw (.sessionMismatch sess sh.session)
  -- Compute challenge and aggregate
  let w : S.Public := (reveals.map (·.w_i)).sum
  let c : S.Challenge := S.hash m pk Sset (commits.map (·.commitW)) w
  let sig := aggregateSignature S c Sset (commits.map (·.commitW)) shares
  pure sig

/-!
## Threshold Context

ThresholdCtx bundles:
- active: the Finset of participating signers
- t: the threshold (min signers needed)
- mode: all-parties vs general threshold
- strategy: how to aggregate (ones vs lagrange)
- proofs: t ≤ |active| and strategy alignment

This allows the protocol to choose the efficient path (simple sum) when
possible, while maintaining invariants needed for correctness.
-/

/-- Signing mode: all-parties (n-of-n) or general threshold (t-of-n). -/
inductive SignMode | all | threshold
deriving DecidableEq

/-- Threshold context with proofs of well-formedness.
    Carries both configuration and validity guarantees. -/
structure ThresholdCtx (S : Scheme) [DecidableEq S.PartyId] where
  active     : Finset S.PartyId    -- participating signers
  t          : Nat                 -- threshold (t = |active| for n-of-n)
  mode       : SignMode            -- n-of-n vs t-of-n
  strategy   : CoeffStrategy S     -- aggregation method
  card_ge    : t ≤ active.card     -- proof: have enough signers
  strategy_ok : strategyOK S active.toList strategy -- coeffs align

/-- Membership predicate: all shares from declared active set. -/
def sharesFromActive (S : Scheme) [DecidableEq S.PartyId]
  (ctx : ThresholdCtx S) (shares : List (SignShareMsg S)) : Prop :=
  ∀ sh ∈ shares, sh.sender ∈ ctx.active

/-- Decidable instance for sharesFromActive. -/
instance sharesFromActiveDecidable (S : Scheme) [DecidableEq S.PartyId]
  (ctx : ThresholdCtx S) (shares : List (SignShareMsg S))
  : Decidable (sharesFromActive S ctx shares) :=
  List.decidableBAll shares (fun sh => sh.sender ∈ ctx.active)

/-!
### Context Constructors

Smart constructors build ThresholdCtx with proofs:
- mkAllCtx: for n-of-n (all parties sign)
- mkThresholdCtx: for t-of-n with pre-supplied coefficients
- mkThresholdCtxComputed: recomputes Lagrange coeffs from active set
-/

/-- Build n-of-n context: threshold = |active|, strategy = ones. -/
def mkAllCtx (S : Scheme) [DecidableEq S.PartyId]
  (active : Finset S.PartyId) : ThresholdCtx S :=
{ active := active,
  t := active.card,
  mode := SignMode.all,
  strategy := CoeffStrategy.ones,
  card_ge := by simp,
  strategy_ok := by trivial }

/-- Build t-of-n context with pre-supplied Lagrange coefficients.
    Caller provides proofs that coeffs align with active set. -/
def mkThresholdCtx
  (S : Scheme) [DecidableEq S.PartyId]
  (active : Finset S.PartyId)
  (t : Nat)
  (coeffs : List (LagrangeCoeff S))
  (hcard : t ≤ active.card)
  (halign : coeffs.map (·.pid) = active.toList)
  (hlen : coeffs.length = active.toList.length)
  : ThresholdCtx S :=
{ active := active,
  t := t,
  mode := SignMode.threshold,
  strategy := CoeffStrategy.lagrange coeffs,
  card_ge := hcard,
  strategy_ok := by simp [strategyOK, halign, hlen] }

/-- Extract Lagrange coefficients from existing context.
    Recomputes λ_i for each party in active set. -/
noncomputable def coeffsFromCtx
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId] [DecidableEq S.Scalar]
  (ctx : ThresholdCtx S)
  (pidToScalar : S.PartyId → S.Scalar) : List (LagrangeCoeff S) :=
  ctx.active.toList.map (fun pid =>
    { pid := pid, lambda := lagrangeCoeffAtZero S pidToScalar ctx.active.toList pid })

/-- Build t-of-n context by computing fresh Lagrange coefficients.
    Requires Field for division in Lagrange formula. -/
noncomputable def mkThresholdCtxComputed
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId] [DecidableEq S.Scalar]
  (active : Finset S.PartyId)
  (t : Nat)
  (pidToScalar : S.PartyId → S.Scalar)
  (hcard : t ≤ active.card) : ThresholdCtx S :=
  let coeffs := active.toList.map (fun pid =>
    { pid := pid, lambda := lagrangeCoeffAtZero S pidToScalar active.toList pid })
  have hlen : coeffs.length = active.toList.length := List.length_map _ _
  have hpid : coeffs.map (·.pid) = active.toList := by
    simp only [List.map_map, Function.comp]
    exact List.map_id' (fun _ => rfl)
  mkThresholdCtx S active t coeffs hcard hpid hlen

/-- Refresh context with fresh coefficients (same active set/threshold). -/
noncomputable def refreshThresholdCtx
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId] [DecidableEq S.Scalar]
  (pidToScalar : S.PartyId → S.Scalar)
  (ctx : ThresholdCtx S) : ThresholdCtx S :=
  mkThresholdCtxComputed S ctx.active ctx.t pidToScalar ctx.card_ge

/-!
### Context-Based Aggregation

These functions use ThresholdCtx to select the right aggregation path
and validate shares against the declared active set.
-/

/-- Aggregate using context's strategy after membership validation.
    Returns none if shares aren't from active set. -/
noncomputable def aggregateSignatureWithCtx
  (S    : Scheme) [DecidableEq S.PartyId]
  (c    : S.Challenge)
  (ctx  : ThresholdCtx S)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  : Option (Signature S) :=
  if _hfrom : sharesFromActive S ctx shares then
    aggregateWithStrategy S c ctx.active.toList commits shares ctx.strategy
  else
    none

/-- Direct Lagrange aggregation using context's active set.
    Assumes coeffs are already validated. -/
noncomputable def aggregateSignatureLagrangeThresh
  (S    : Scheme) [DecidableEq S.PartyId]
  (c    : S.Challenge)
  (ctx  : ThresholdCtx S)
  (commits : List S.Commitment)
  (coeffs : List (LagrangeCoeff S))
  (shares : List (SignShareMsg S))
  : Signature S :=
  aggregateSignatureLagrange S c ctx.active.toList commits coeffs shares

/-!
## CRDT Pipeline Output

SignatureDone wraps the final signature for the CRDT pipeline.
Indicates signing protocol reached completion.
-/

/-- Final signature wrapper for CRDT done state. -/
structure SignatureDone (S : Scheme) where
  sig : Signature S

/-- DoneState alias for CRDT phase state. -/
abbrev DoneState := SignatureDone

/-- DoneState merge: idempotent (signature already finalized). -/
instance (S : Scheme) : Join (DoneState S) :=
  ⟨fun a _ => a⟩

instance (S : Scheme) : LE (DoneState S) := ⟨fun _ _ => True⟩

end IceNine.Protocol
