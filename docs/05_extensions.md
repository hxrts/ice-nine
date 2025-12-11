# Extensions

The core protocol supports several extensions. These extensions address operational requirements beyond basic signing. They enable share management and enhanced privacy. All extension state structures form semilattices that merge via join.

## Error Handling

The `Protocol/Error.lean` module provides unified error handling patterns across the protocol.

### BlameableError Typeclass

Errors that can identify a misbehaving party implement the `BlameableError` typeclass:

```lean
class BlameableError (E : Type*) (PartyId : Type*) where
  blamedParty : E → Option PartyId

instance : BlameableError (DkgError PartyId) PartyId where
  blamedParty
    | .lengthMismatch => none
    | .duplicatePids => none
    | .commitMismatch p => some p

instance : BlameableError (Complaint PartyId) PartyId where
  blamedParty c := some c.accused

instance : BlameableError (VSS.VSSError PartyId) PartyId where
  blamedParty
    | .shareVerificationFailed accused _ => some accused
    | .missingCommitment p => some p
    | .missingShare from _ => some from
    | .thresholdMismatch _ _ => none
    | .duplicateDealer p => some p
```

### Cheater Detection Modes

Following FROST, we provide configurable cheater detection:

```lean
inductive CheaterDetectionMode
  | disabled      -- No blame tracking (best performance)
  | firstCheater  -- Stop after finding one cheater (good balance)
  | allCheaters   -- Exhaustively identify all cheaters (complete but slower)

structure ProtocolConfig where
  cheaterDetection : CheaterDetectionMode := .firstCheater
  maxErrors : Nat := 0  -- 0 = unlimited

def ProtocolConfig.default : ProtocolConfig
def ProtocolConfig.highSecurity : ProtocolConfig   -- allCheaters mode
def ProtocolConfig.performance : ProtocolConfig    -- disabled mode
```

### Error Aggregation

Utilities for collecting and analyzing errors across protocol execution:

```lean
/-- Count how many errors blame a specific party -/
def countBlame (errors : List E) (party : PartyId) : Nat

/-- Get all unique blamed parties from a list of errors -/
def allBlamedParties (errors : List E) : List PartyId

/-- Collect blame respecting detection mode -/
def collectBlame (config : ProtocolConfig) (errors : List E) : BlameResult PartyId
```

### Error Categories

| Module | Type | Category | Description |
|--------|------|----------|-------------|
| DKGCore | `DkgError` | Fatal | Protocol abort required |
| DKGThreshold | `Complaint` | Recoverable | Party exclusion possible |
| VSS | `VSSError` | Fatal/Recoverable | Depends on complaint count |
| RepairCoord | `ContribCommitResult` | Result | Processing outcome |

## Security Markers

The `Protocol/Core.lean` module provides typeclass markers for implementation security requirements. These markers document FFI implementation obligations.

### Zeroizable Typeclass

Marks types containing secret material that must be securely erased from memory after use.

```lean
class Zeroizable (α : Type*) where
  needsZeroization : Bool := true

instance : Zeroizable (SecretBox α)
```

**Implementation guidance:**

| Platform | API |
|----------|-----|
| Rust | `zeroize::Zeroize` trait, `ZeroizeOnDrop` |
| C | `explicit_bzero()`, `SecureZeroMemory()` |
| POSIX | `explicit_bzero()` |
| Windows | `SecureZeroMemory()` |

### ConstantTimeEq Typeclass

Marks types requiring constant-time equality comparison to prevent timing side-channels.

```lean
class ConstantTimeEq (α : Type*) where
  requiresConstantTime : Bool := true

instance : ConstantTimeEq (SecretBox α)
```

**Implementation guidance:**

- Use `subtle::ConstantTimeEq` in Rust
- Use `CRYPTO_memcmp()` from OpenSSL
- Never use early-exit comparison loops
- Avoid branching on secret-dependent values

## Serialization

The `Protocol/Serialize.lean` module provides type-safe serialization for network transport.

### Serialization Headers

Messages include headers for version and scheme identification:

```lean
inductive SchemeId
  | mlDsa44 | mlDsa65 | mlDsa87 | custom (id : ByteArray)

structure SerializationHeader where
  version : UInt8       -- protocol version (currently 1)
  schemeId : SchemeId   -- parameter set identifier

class SerializableWithHeader (α : Type*) extends Serializable α where
  header : SerializationHeader
  toBytesWithHeader : α → ByteArray
  fromBytesWithHeader : ByteArray → Option α
```

This enables:
- **Version negotiation**: Detect incompatible protocol versions
- **Parameter validation**: Verify scheme compatibility before deserializing
- **Safe upgrades**: Add new schemes without breaking existing deployments

### Serializable Typeclass

```lean
class Serializable (α : Type*) where
  toBytes : α → ByteArray
  fromBytes : ByteArray → Option α
```

Implementations are provided for primitives (`Nat`, `Int`, `ByteArray`), compound types (`Option`, `List`), and all protocol messages.

### Wire Format

The wire format uses little-endian encoding with explicit length prefixes:

| Type | Format |
|------|--------|
| Nat | 8-byte little-endian |
| Int | 8-byte little-endian (two's complement) |
| List α | 4-byte length + concatenated elements |
| Option α | 1-byte tag (0=none, 1=some) + element if some |

### Message Wrapping

Messages are wrapped with type tags for network transport:

```lean
inductive MessageTag
  | dkgCommit | dkgReveal
  | signCommit | signReveal | signShare
  | signature
  | abort

structure WrappedMessage where
  tag : MessageTag
  payload : ByteArray

def WrappedMessage.toBytes (msg : WrappedMessage) : ByteArray :=
  -- tag (1 byte) + length (4 bytes) + payload
```

**Security Note**: Deserialization is a potential attack surface. All `fromBytes` implementations validate input lengths and return `none` on malformed input.

## Complaints

The complaint mechanism identifies misbehaving parties. It activates when protocol invariants are violated.

### Complaint Types

Two complaint variants cover the main failure modes.

```lean
inductive Complaint (PartyId : Type) where
  | openingMismatch (accused : PartyId)
  | missingReveal (accused : PartyId)
```

### Complaint Triggers

A party files a complaint under the following conditions.

**Invalid commitment opening.** Party $P_j$ reveals a pair $(\mathsf{pk}_j, r_j)$ that does not match its commitment $\mathsf{Com}_j$. Generates `openingMismatch`.

**Missing message.** Party $P_j$ fails to send a required message within the timeout. Generates `missingReveal`.

**Inconsistent session.** The participant set $S$ differs from the expected set.

**Invalid partial signature.** Party $P_j$ produces a partial signature $z_j$ that fails verification.

### Aggregation with Complaints

DKG aggregation returns either the public key or a list of complaints identifying misbehaving parties.

```lean
def dkgAggregateWithComplaints
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  : Except (List (Complaint S.PartyId)) S.Public
```

### Complaint Resolution

When a party files a complaint the protocol may proceed in different ways.

**Abort.** All parties discard the current session. They may retry with a new session excluding the accused party.

**Exclude.** The accused party is removed from the participant set. The remaining parties continue if the threshold is still met.

**Penalize.** In applications with economic stakes the accused party may lose a deposit or face other penalties.

### Complaint Verification

A complaint is verifiable when it includes evidence. For a commitment opening failure the evidence is the commitment, the revealed pair, and a proof that they do not match. Other parties can independently verify the complaint.

## Share Refresh

Share refresh updates the shares without changing the public key. This procedure provides proactive security. Even if an adversary compromises old shares the refreshed shares are independent.

### Mask Function Structure

Masks are represented as functions from party identifier to secret.

```lean
structure MaskFn (S : Scheme) :=
  (mask : S.PartyId → S.Secret)

instance (S : Scheme) : Join (MaskFn S) :=
  ⟨fun a b => { mask := fun pid => a.mask pid + b.mask pid }⟩
```

The join merges masks by pointwise addition.

### Zero-Sum Mask Invariant

The zero-sum property is captured in a dependent structure.

```lean
structure ZeroSumMaskFn (S : Scheme) (active : Finset S.PartyId) :=
  (fn : MaskFn S)
  (sum_zero : (active.toList.map (fun pid => fn.mask pid)).sum = 0)

instance (S : Scheme) (active : Finset S.PartyId) : Join (ZeroSumMaskFn S active)
```

Merging zero-sum masks preserves zero-sum on the same active set.

### Refresh Overview

Each party $P_i$ holds a share $s_i$. After refresh each party holds a new share $s'_i = s_i + \delta_i$. The masks $\delta_i$ sum to zero.

$$\sum_i \delta_i = 0$$

This ensures the master secret is unchanged.

$$\sum_i s'_i = \sum_i (s_i + \delta_i) = \sum_i s_i + \sum_i \delta_i = s + 0 = s$$

### Refresh Function

Applies a mask to each share and recomputes the corresponding public share.

```lean
def refreshShares
  (S : Scheme)
  (m : MaskFn S)
  (shares : List (KeyShare S)) : List (KeyShare S) :=
  shares.map (fun ks =>
    let sk' := ks.sk_i + m.mask ks.pid
    let pk' := S.A sk'
    { ks with sk_i := sk', pk_i := pk' })
```

### Mask Generation

The masks must sum to zero. One approach is as follows.

1. Each party $P_i$ samples a random mask contribution $\mu_i \in \mathcal{S}$.
2. Parties run a protocol to compute a common offset $\mu = \sum_i \mu_i$.
3. Each party sets $\delta_i = \mu_i - \mu / n$ in a way that ensures $\sum_i \delta_i = 0$.

An alternative uses pairwise contributions. Party $P_i$ sends $\delta_{ij}$ to party $P_j$ and receives $\delta_{ji}$ from $P_j$. The net contribution is $\delta_i = \sum_{j \neq i} (\delta_{ij} - \delta_{ji})$. These contributions cancel pairwise.

### Public Share Update

After refresh each party computes its new public share.

$$\mathsf{pk}'_i = A(s'_i) = A(s_i + \delta_i) = A(s_i) + A(\delta_i) = \mathsf{pk}_i + A(\delta_i)$$

The global public key remains unchanged because

$$\sum_i \mathsf{pk}'_i = \sum_i \mathsf{pk}_i + \sum_i A(\delta_i) = \mathsf{pk} + A\left(\sum_i \delta_i\right) = \mathsf{pk} + A(0) = \mathsf{pk}$$

### Refresh Protocol

A full refresh protocol runs as follows.

1. Each party generates its mask contribution.
2. Parties exchange commitments to their contributions.
3. Parties reveal their contributions.
4. Each party verifies all commitments.
5. Each party computes its new share.
6. Parties publish new commitments to their public shares.
7. External verifiers can check the consistency of the new public shares.

### Refresh Coordination Protocol

The `Protocol/RefreshCoord.lean` module provides a distributed protocol for generating zero-sum masks without a trusted coordinator.

**Phases:**
1. **Commit**: Each party commits to their random mask
2. **Reveal**: Parties reveal masks after all commits received
3. **Adjust**: Coordinator computes adjustment to achieve zero-sum
4. **Apply**: All parties apply masks to their shares

**CRDT Design:** Uses `MsgMap` for commits and reveals to ensure at most one message per party. This makes conflicting messages un-expressable at the type level.

```lean
abbrev MaskCommitMap (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] :=
  MsgMap S (MaskCommitMsg S)

abbrev MaskRevealMap (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] :=
  MsgMap S (MaskRevealMsg S)

structure RefreshRoundState (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] where
  phase : RefreshPhase
  parties : List S.PartyId
  roundNum : Nat
  coordStrategy : CoordinatorStrategy S.PartyId
  maskCommits : MaskCommitMap S    -- at most one per party
  maskReveals : MaskRevealMap S    -- at most one per party
  adjustment : Option (AdjustmentMsg S)
```

**Commitment Design:** The protocol commits to `A(mask)` (the public image) rather than the mask itself. This enables:
- Public verifiability without revealing the secret mask
- Consistency with DKG (which commits to public shares)
- Simple zero-sum verification via `A(Σ m_i)`

**Architecture: Separated CRDT and Validation**

The protocol separates concerns into two layers:

1. **CRDT Layer** - Pure merge semantics for replication/networking
2. **Validation Layer** - Conflict detection for auditing/security

```lean
-- CRDT merge: idempotent, always succeeds, silently ignores duplicates
def processCommit (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) (msg : MaskCommitMsg S)
    : RefreshRoundState S

def processReveal (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) (msg : MaskRevealMsg S)
    : RefreshRoundState S

-- Validation: detect conflicts without modifying state
def detectCommitConflict (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) (msg : MaskCommitMsg S)
    : Option (MaskCommitMsg S)

def validateCommit (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) (msg : MaskCommitMsg S)
    : Option (CommitValidationError S)

-- Combined: merge + validation in one call
def processCommitValidated (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) (msg : MaskCommitMsg S)
    : RefreshRoundState S × Option (CommitValidationError S)
```

**Design Rationale:**
- CRDT functions can be used directly for networking without error handling in merge path
- Validation is explicit and composable—call it when you need it
- Follows "make illegal states unrepresentable" at CRDT level, "detect suspicious patterns" separately

**Coordinator Selection:**
```lean
inductive CoordinatorStrategy (PartyId : Type*)
  | fixed (pid : PartyId)      -- always same coordinator
  | roundRobin (round : Nat)   -- rotate based on round number
  | random (seed : Nat)        -- pseudo-random selection
```

**Zero-Sum Verification:**
The coordinator computes adjustment $m_n = -\sum_{i \neq n} m_i$ ensuring $\sum_i m_i = 0$:

```lean
def computeAdjustment (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    [DecidableEq S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S) : Option S.Secret :=
  if st.phase = .adjust then
    let coord := st.coordinator
    let otherMasks := st.maskReveals.toList.filter (fun r => r.sender ≠ coord)
    let sumOthers := (otherMasks.map (·.mask)).sum
    some (-sumOthers)
  else none
```

### DKG-Based Refresh Protocol

The `Protocol/RefreshDKG.lean` module provides a fully distributed refresh protocol without a trusted coordinator. Each party contributes a zero-polynomial (polynomial with constant term 0), ensuring the master secret remains unchanged while all shares are updated.

**Three-Round Protocol:**

1. **Round 1 (Commit)**: Each party samples a random polynomial $f_i(x)$ with $f_i(0) = 0$ and broadcasts a commitment to its polynomial coefficients.

2. **Round 2 (Share)**: Each party evaluates its polynomial at all other parties' identifiers and sends the shares privately.

3. **Round 3 (Verify & Apply)**: Each party verifies received shares against commitments and computes its refresh delta as the sum of all received shares.

```lean
structure RefreshLocalState (S : Scheme) where
  pid : S.PartyId
  coefficients : List S.Secret  -- [0, a₁, a₂, ..., a_{t-1}]
  opening : S.Opening

structure RefreshDelta (S : Scheme) where
  pid : S.PartyId
  delta : S.Secret  -- sum of all f_j(pid)

def refreshRound1 (S : Scheme) (pid : S.PartyId)
    (randomCoeffs : List S.Secret) (opening : S.Opening)
    : RefreshLocalState S × RefreshCommitMsg S

def refreshRound3 (S : Scheme)
    (st : RefreshLocalState S)
    (commits : List (RefreshCommitMsg S))
    (shares : List (RefreshShareMsg S))
    : Except (RefreshDKGError S.PartyId) (RefreshDelta S)
```

**Security Properties:**

- **No trusted coordinator**: Unlike `RefreshCoord.lean`, no single party learns all masks
- **Verifiable**: Polynomial commitments allow verification of received shares
- **Zero-sum by construction**: Since each $f_i(0) = 0$, the sum of deltas preserves the master secret:
  $$\sum_j \delta_j = \sum_j \sum_i f_i(j) = \sum_i \sum_j f_i(j) = \sum_i f_i(0) \cdot n = 0$$

**Verification:**

```lean
def verifyZeroSum (S : Scheme) (deltas : List (RefreshDelta S)) : Bool :=
  (deltas.map (·.delta)).sum = 0
```

### Public Key Invariance Theorem

If the mask sums to zero over the participant list, the global public key is unchanged.

```lean
lemma refresh_pk_unchanged
  (S : Scheme)
  (m : MaskFn S)
  (shares : List (KeyShare S))
  (hsum : (shares.map (fun ks => m.mask ks.pid)).sum = 0) :
  let refreshed := refreshShares S m shares
  (refreshed.foldl (fun acc ks => acc + ks.pk_i) (0 : S.Public)) =
  (shares.foldl (fun acc ks => acc + ks.pk_i) (0 : S.Public))
```

### Refresh State (CRDT)

Refresh state forms a semilattice for conflict-free replication.

```lean
structure RefreshState (S : Scheme) :=
  (mask : MaskFn S)

instance (S : Scheme) : Join (RefreshState S)
instance (S : Scheme) : SemilatticeSup (RefreshState S)
```

### Security Properties

**Forward secrecy.** Old shares reveal nothing about new shares.

**Backward secrecy.** New shares reveal nothing about old shares.

**Invariant preservation.** The master secret and global public key are unchanged.

## Share Repair

Share repair allows a party to recover a lost share. The recovering party receives help from other parties.

### Repair Request Structure

Messages for initiating and responding to repair requests. Bundles merge via list append.

```lean
structure RepairRequest (S : Scheme) :=
  (requester : S.PartyId)
  (knownPk_i : S.Public)  -- The public share is still known

structure RepairMsg (S : Scheme) where
  sender : S.PartyId  -- helper party
  target : S.PartyId  -- requester (for routing)
  delta  : S.Secret   -- weighted share contribution

structure RepairBundle (S : Scheme) :=
  (msgs : List (RepairMsg S))

instance (S : Scheme) : Join (RepairBundle S) := ⟨fun a b => ⟨a.msgs ++ b.msgs⟩⟩
```

### Repair Session State

The repair session tracks protocol progress with CRDT merge semantics.

```lean
structure RepairSession (S : Scheme) :=
  (request   : RepairRequest S)
  (helpers   : Finset S.PartyId)
  (received  : RepairBundle S)
  (threshold : Nat)

instance (S : Scheme) : Join (RepairSession S)
```

### Repair Scenario

Party $P_i$ has lost its share $s_i$. It wants to recover the share without other parties learning it.

### Helper Protocol

Each helper $P_j$ sends a masked delta to $P_i$. The deltas are structured so that their sum equals $s_i$.

Let $\Delta_{ji}$ denote the message from $P_j$ to $P_i$. The messages satisfy

$$\sum_{j \neq i} \Delta_{ji} = s_i$$

### Repair Function

Sums the deltas from all helper messages to reconstruct the lost share.

```lean
def repairShare
  (S : Scheme)
  (msgs : List (RepairMsg S))
  : S.Secret :=
  msgs.foldl (fun acc m => acc + m.delta) (0 : S.Secret)
```

### Correctness

The repaired share equals the original when deltas sum correctly.

```lean
lemma repair_correct
  (S : Scheme)
  (msgs : List (RepairMsg S))
  (sk_i : S.Secret)
  (h : msgs.foldl (fun acc m => acc + m.delta) (0 : S.Secret) = sk_i) :
  repairShare S msgs = sk_i
```

### Privacy (Zero-Sum Masks)

Additional zero-sum masks do not change the repaired value:

```lean
lemma repair_masked_zero
  (S : Scheme)
  (msgs : List (RepairMsg S))
  (mask : List S.Secret)
  (hmask : mask.sum = 0)
  (hlen : mask.length = msgs.length) :
  repairShare S (List.zipWith (fun m z => { m with delta := m.delta + z }) msgs mask)
    = repairShare S msgs
```

### Construction

One construction uses Lagrange interpolation. If the shares are polynomial shares evaluated at distinct points then any $t$ parties can reconstruct the share at any point.

The Lagrange coefficient for party $i$ evaluating at 0 over set $S$ is:

$$\lambda_i^S = \prod_{j \in S, j \neq i} \frac{x_j}{x_j - x_i}$$

These coefficients satisfy the partition of unity property: $\sum_{i \in S} \lambda_i^S = 1$.

The implementation verifies these properties against Mathlib's `Lagrange` module. These lemmas confirm equivalence with the standard formulation and the partition of unity property.

```lean
-- Our formula equals Mathlib's basis polynomial evaluated at 0
lemma lagrangeCoeffAtZero_eq_basis_eval :
  lagrangeCoeffAtZero S pidToScalar Sset i = (Lagrange.basis s v i).eval 0

-- Lagrange coefficients sum to 1 (partition of unity)
lemma lagrangeCoeffs_sum_one (hs : s.Nonempty) :
  (∑ i ∈ s, (Lagrange.basis s v i).eval 0) = 1

-- Weighted sum reconstructs polynomial at 0
lemma lagrange_interpolation_at_zero :
  (∑ i ∈ s, (Lagrange.basis s v i).eval 0 * r i) = p.eval 0
```

For additive shares a simpler approach works. Each helper $P_j$ sends a random share of its own share $s_j$. The recovering party combines these to reconstruct its share through a pre-established linear relation.

### Helper Contribution Function

Each helper scales its share by a Lagrange coefficient and sends the result.

```lean
def helperContribution
  (S : Scheme)
  (helper : KeyShare S)
  (requester : S.PartyId)
  (coefficient : S.Scalar)
  : RepairMsg S :=
  { from  := helper.pid
  , to    := requester
  , delta := coefficient • helper.sk_i }
```

### Verification

Checks that the repaired secret maps to the expected public share.

```lean
def verifyRepairedShare
  (S : Scheme)
  (repairedSk : S.Secret)
  (expectedPk : S.Public)
  : Prop :=
  S.A repairedSk = expectedPk
```

### Threshold Completion

Checks whether enough helpers have responded and attempts to complete the repair.

```lean
def hasEnoughHelpers
  (S : Scheme) [DecidableEq S.PartyId]
  (session : RepairSession S)
  : Bool :=
  (helperPids S session.received.msgs).length ≥ session.threshold

def tryCompleteRepair
  (S : Scheme) [DecidableEq S.PartyId]
  (session : RepairSession S)
  : Option S.Secret
```

### Security

**Privacy.** No single helper learns $s_i$. Zero-sum masking ensures that additional randomness does not affect the reconstructed value.

**Correctness.** The recovered share equals the original share. Verified via `verifyRepairedShare`.

**Threshold.** At least $t$ helpers must participate. Enforced by `hasEnoughHelpers`.

**Robustness.** If threshold is met, `tryCompleteRepair` returns `Some`.

### Repair Protocol Steps

1. Party $P_i$ broadcasts a `RepairRequest` with its known public share.
2. Each helper $P_j$ computes its delta via `helperContribution`.
3. Each helper sends the `RepairMsg` to $P_i$ over a secure channel.
4. Party $P_i$ collects messages in a `RepairSession` (CRDT-mergeable).
5. When `hasEnoughHelpers` returns true, party $P_i$ calls `tryCompleteRepair`.
6. Party $P_i$ verifies $A(s_i) = \mathsf{pk}_i$ via `verifyRepairedShare`.

### Repair Coordination Protocol

The `Protocol/RepairCoord.lean` module provides a commit-reveal protocol for coordinating repair contributions.

**Phases:**
1. **Request**: Requester broadcasts repair request with known $pk_i$
2. **Commit**: Helpers commit to their Lagrange-weighted contributions
3. **Reveal**: Helpers reveal contributions after all commits received
4. **Verify**: Requester verifies $A(sk_i) = pk_i$

**CRDT Design:** Uses `MsgMap` for commits and reveals to ensure at most one message per helper. This makes conflicting messages un-expressable at the type level.

```lean
abbrev ContribCommitMap (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] :=
  MsgMap S (ContribCommitMsg S)

abbrev ContribRevealMap (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] :=
  MsgMap S (ContribRevealMsg S)

inductive RepairPhase
  | request | commit | reveal | verify | done

structure RepairCoordState (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] where
  phase : RepairPhase
  request : RepairRequest S
  helpers : List S.PartyId
  threshold : Nat
  commits : ContribCommitMap S    -- at most one per helper
  reveals : ContribRevealMap S    -- at most one per helper
  repairedShare : Option S.Secret
```

**Architecture: Separated CRDT and Validation**

Like RefreshCoord, RepairCoord separates CRDT merge from validation:

```lean
-- CRDT merge: idempotent, always succeeds, silently ignores duplicates/non-helpers
def processContribCommit (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RepairCoordState S) (msg : ContribCommitMsg S)
    : RepairCoordState S

def processContribReveal (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RepairCoordState S) (msg : ContribRevealMsg S)
    : RepairCoordState S

-- Validation: detect conflicts without modifying state
def detectContribCommitConflict (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RepairCoordState S) (msg : ContribCommitMsg S)
    : Option (ContribCommitMsg S)

def validateContribCommit (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RepairCoordState S) (msg : ContribCommitMsg S)
    : Option (ContribCommitValidationError S)  -- wrongPhase | notHelper | conflict

-- Combined: merge + validation in one call
def processContribCommitValidated (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RepairCoordState S) (msg : ContribCommitMsg S)
    : RepairCoordState S × Option (ContribCommitValidationError S)
```

**Usage Patterns:**
- **Networking**: Use `processContribCommit`/`processContribReveal` directly for replication
- **Auditing**: Call `detectContribCommitConflict` to check for duplicate messages
- **Strict mode**: Use `processContribCommitValidated` for both merge and error reporting

**Helper State:**
Each helper maintains local state for participation:

```lean
structure HelperLocalState (S : Scheme) where
  helperId : S.PartyId
  keyShare : KeyShare S
  lagrangeCoeff : S.Scalar
  contribution : S.Secret        -- λ_j · sk_j
  commitment : S.Commitment
  opening : S.Opening
```

**Lagrange Coefficient Computation:**
Uses the unified `Protocol/Lagrange.lean` module:
```lean
def lagrangeCoefficient [Field F] [DecidableEq F]
    (partyScalar : F) (otherScalars : List F) : F :=
  otherScalars.foldl (fun acc m =>
    if m = partyScalar then acc
    else acc * (m / (m - partyScalar))) 1
```

**Transcript Creation:**
The `createTranscript` function extracts ordered lists from MsgMap for verification:

```lean
def createTranscript (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RepairCoordState S) : Option (RepairTranscript S) :=
  if st.phase = .done then
    some { commits := st.commits.toList.map (·.2)
           reveals := st.reveals.toList.map (·.2)
           repairedShare := st.repairedShare.getD default }
  else none
```

**Verification:**
The repaired share is verified against the known public share:

```lean
def completeRepair (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    [DecidableEq S.Public]
    (st : RepairCoordState S) : RepairCoordState S :=
  if st.phase = .verify then
    let repairedSk := aggregateContributions S st.reveals.toList
    if S.A repairedSk = st.request.knownPk_i then
      { st with repairedShare := some repairedSk, phase := .done }
    else st
  else st
```

## Rerandomization

Rerandomization adds privacy by masking shares and nonces. It prevents linking between signing sessions.

### Rerandomization Masks Structure

Holds zero-sum masks for both shares and nonces. Masks merge by pointwise addition.

```lean
structure RerandMasks (S : Scheme) :=
  (shareMask : S.PartyId → S.Secret)
  (nonceMask : S.PartyId → S.Secret)
  (shareSumZero : ∀ (Sset : List S.PartyId), (Sset.map shareMask).sum = 0)
  (nonceSumZero : ∀ (Sset : List S.PartyId), (Sset.map nonceMask).sum = 0)

instance (S : Scheme) : Join (RerandMasks S)
```

### Motivation

Without rerandomization the same shares produce related signatures. An observer might link signatures to the same key or signer set. Rerandomization breaks this linkage.

### State Rerandomization

Applies masks to both the nonce and share within a signing state.

```lean
def rerandState
  (S : Scheme)
  (masks : RerandMasks S)
  (st : SignLocalState S) : SignLocalState S :=
{ st with
  y_i := st.y_i + masks.nonceMask st.share.pid,
  w_i := S.A (st.y_i + masks.nonceMask st.share.pid),
  share := { st.share with
    sk_i := st.share.sk_i + masks.shareMask st.share.pid,
    pk_i := S.A (st.share.sk_i + masks.shareMask st.share.pid) } }
```

### Share Rerandomization

Before signing each party adds a mask to its share.

$$s'_i = s_i + \delta_i$$

The masks must sum to zero as in refresh. The signing protocol uses the masked shares. The verification equation remains valid because the master secret is unchanged.

### Nonce Rerandomization

Similarly parties can add masks to their nonces.

$$y'_i = y_i + \gamma_i$$

If $\sum_i \gamma_i = 0$ then the aggregated nonce is unchanged.

$$w = \sum_i A(y'_i) = \sum_i A(y_i) + A\left(\sum_i \gamma_i\right) = \sum_i A(y_i) + 0$$

### Signature Preservation Theorem

Zero-sum masks cancel out in the aggregated signature.

```lean
lemma rerand_preserves_sig
  (S : Scheme)
  (masks : RerandMasks S)
  (Sset : List S.PartyId)
  (c : S.Challenge)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S)) :
  (shares.map (fun sh => masks.shareMask sh.sender)).sum = 0 →
  aggregateSignature S c Sset commits
    (shares.map (fun sh => { sh with z_i := sh.z_i + masks.shareMask sh.sender }))
    = aggregateSignature S c Sset commits shares
```

### Combined Rerandomization

A full rerandomization applies masks to both shares and nonces. The masks must satisfy the zero-sum property independently.

$$\sum_i \delta_i = 0$$
$$\sum_i \gamma_i = 0$$

### Unlinkability

Rerandomization provides unlinkability. An adversary who sees multiple signatures cannot determine if they were produced by the same set of parties. Each session appears independent.

### Protocol Integration

Rerandomization integrates into the signing protocol as follows.

1. Before round one parties agree on a session identifier.
2. Each party derives its masks from the session identifier and randomness.
3. Parties exchange commitments to their masked values.
4. The signing protocol proceeds with masked shares and nonces.
5. The final signature is identical to one produced without rerandomization.

## Party Addition and Removal

The protocol can add or remove parties from the signer set.

### Party Removal

To remove party $P_k$ the remaining parties redistribute its share. This is equivalent to a repair followed by a refresh. The share $s_k$ is recovered and then split among the remaining parties.

### Party Addition

To add party $P_{n+1}$ the existing parties run a refresh that creates a new share. The new share $s_{n+1}$ is generated such that the shares still sum to the master secret.

### Threshold Adjustment

Changing the threshold requires restructuring the shares. Moving from $t$-of-$n$ to $t'$-of-$n$ requires a new secret sharing polynomial of degree $t'-1$. This is more complex than simple refresh.

## Key Rotation

Key rotation changes the master secret and public key. Unlike refresh which preserves the key rotation generates a new key.

### Rotation Procedure

1. Parties run a new DKG protocol.
2. The new protocol produces fresh shares $s'_i$ for a new secret $s'$.
3. The new public key is $\mathsf{pk}' = A(s')$.
4. External systems update to use the new public key.

### Migration

Applications must migrate from the old key to the new key. Signatures under the old key remain valid. New signatures use the new key.

## Composite State (CRDT)

Protocol phase state combines with refresh, repair, and rerandomization state in a product semilattice. Merge is provided by the product semilattice instances.

```lean
abbrev CompositeState (S : Scheme) (p : Phase) :=
  (State S p) × RefreshState S × RepairBundle S × RerandMasks S
```

## Threshold-Aware Merge

For threshold protocols, the `ShareWithCtx` structure couples share state with threshold context. When two replicas merge, the active signer sets may differ. The merge must:

1. Union the active sets: `merged.active = a.active ∪ b.active`
2. Preserve threshold: `merged.t = max(a.t, b.t)`
3. Prove validity: `merged.t ≤ |merged.active|`
4. Recompute coefficients: Lagrange $\lambda_i$ depend on the signer set

### Merge Strategies

Three merge strategies are provided:

**Conservative merge (ones):** Falls back to n-of-n with simple sum. No field required but loses threshold efficiency.

```lean
def mergeShareWithCtxOnes (S : Scheme) [DecidableEq S.PartyId]
  (a b : ShareWithCtx S) : ShareWithCtx S
```

**Full merge with recompute:** Recomputes Lagrange coefficients for merged set. Preserves t-of-n semantics but requires a Field instance.

```lean
def mergeShareWithCtx
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (pidToScalar : S.PartyId → S.Scalar)
  (a b : ShareWithCtx S) : ShareWithCtx S
```

**Auto merge:** Selects strategy based on field availability. Pass `some inferInstance` for field-backed schemes or `none` for lattice-only builds.

```lean
def mergeShareWithCtxAuto
  (S : Scheme) [DecidableEq S.PartyId]
  (fieldInst : Option (Field S.Scalar))
  (pidToScalar : S.PartyId → S.Scalar)
  (a b : ShareWithCtx S) : ShareWithCtx S
```

### Cardinality Proof Maintenance

The merge must prove that `max(t_a, t_b) ≤ |a.active ∪ b.active|`. This follows from:

- `a.ctx.t ≤ |a.active| ≤ |a.active ∪ b.active|` (subset monotonicity)
- `b.ctx.t ≤ |b.active| ≤ |a.active ∪ b.active|` (subset monotonicity)
- Therefore `max(t_a, t_b) ≤ |merged.active|`

## Type-Indexed Phase Transitions

The `Protocol/PhaseIndexed.lean` module encodes protocol phases at the type level. Invalid phase transitions become compile-time errors rather than runtime failures.

### Phase-Indexed State

State is indexed by the current phase, ensuring only valid operations are available:

```lean
inductive PhaseState (S : Scheme) : Phase → Type where
  | commit  : CommitPhaseData S → PhaseState S .commit
  | reveal  : RevealPhaseData S → PhaseState S .reveal
  | shares  : SharePhaseData S → PhaseState S .shares
  | done    : DonePhaseData S → PhaseState S .done
```

Each phase carries phase-specific data. The runtime phase state (`Protocol/Phase.lean`) uses `MsgMap` for conflict-free message storage, while the type-indexed version uses lists for simpler type signatures:

```lean
-- Type-indexed version (PhaseIndexed.lean) - simpler types
structure CommitPhaseData (S : Scheme) where
  commits : List (DkgCommitMsg S)
  expectedParties : Nat

structure RevealPhaseData (S : Scheme) where
  commits : List (DkgCommitMsg S)
  reveals : List (DkgRevealMsg S)
  commitsComplete : commits.length = expectedParties
  expectedParties : Nat

-- Runtime version (Phase.lean) - conflict-free by construction
structure CommitState (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] where
  commits : CommitMap S   -- MsgMap: at most one per sender

structure RevealState (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] where
  commits : CommitMap S
  reveals : RevealMap S   -- MsgMap: at most one per sender
```

### Type-Safe Transitions

Transitions are functions between specific phase types:

```lean
-- Can only be called when in commit phase
def transitionToReveal (S : Scheme)
    (st : PhaseState S .commit)
    (hready : match st with | .commit data => data.commits.length = data.expectedParties)
    : PhaseState S .reveal

-- Can only be called when in reveal phase
def transitionToShares (S : Scheme)
    (st : PhaseState S .reveal)
    (activeSigners : Finset S.PartyId)
    (message : S.Message)
    (threshold : Nat)
    (hready : match st with | .reveal data => data.reveals.length = data.expectedParties)
    : PhaseState S .shares
```

### Phase Monotonicity

Phase ordering is proven at the type level:

```lean
def Phase.toNat : Phase → Nat
  | .commit => 0 | .reveal => 1 | .shares => 2 | .done => 3

theorem reveal_advances : Phase.commit < Phase.reveal
theorem shares_advances : Phase.reveal < Phase.shares
theorem done_advances : Phase.shares < Phase.done
```

### Benefits

1. **Compile-time safety**: Cannot call `addReveal` in commit phase
2. **Self-documenting**: Type signatures show valid transitions
3. **Proof automation**: Phase ordering proofs are trivial
4. **Extraction functions**: Data access is phase-aware

```lean
def getCommits (S : Scheme) : {p : Phase} → PhaseState S p → List (DkgCommitMsg S)
  | .commit, .commit data => data.commits
  | .reveal, .reveal data => data.commits
  | .shares, .shares data => data.commits
  | .done, .done _ => []
```
