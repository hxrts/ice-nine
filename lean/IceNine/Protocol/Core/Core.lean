/-
# Protocol Core

Core algebraic definitions for the Ice Nine threshold signature protocol.
Defines the abstract Scheme record and basic message types for DKG.

## Module Hierarchy

The Protocol modules are organized in layers:

```
                    Core.lean (Scheme, KeyShare, HashDomain)
                         ↓
    ┌────────────────────┼────────────────────┐
    ↓                    ↓                    ↓
VSSCore.lean         Error.lean          Lagrange.lean
(polynomials,        (BlameableError,    (coefficient
 commitments)        error types)         computation)
    ↓                    ↓                    ↓
    └────────────────────┼────────────────────┘
                         ↓
         ┌───────────────┼───────────────┐
         ↓               ↓               ↓
    DKGCore.lean   SignTypes.lean   Phase.lean
    (basic DKG)    (signing types)  (MsgMap CRDT)
         ↓               ↓               ↓
    DKGThreshold   SignCore.lean   PhaseIndexed
    (with VSS)     (aggregation)   (type-safe)
         ↓               ↓
         └───────┬───────┘
                 ↓
         SignThreshold.lean
         (coefficient strategies)
                 ↓
         SignSession.lean
         (linear session types)
```

**Share Management (extensions)**:
- `Refresh.lean` → `RefreshCoord.lean` (coordinator-based)
- `Refresh.lean` → `RefreshDKG.lean` (distributed)
- `Repair.lean` → `RepairCoord.lean`
- `Rerandomize.lean`

**Composition**:
- `PhaseMerge.lean` (composite CRDT state)
- `ThresholdMerge.lean` (threshold-aware merge)

**Serialization**:
- `Serialize.lean` (wire format)
-/

import Mathlib
import IceNine.Crypto
import IceNine.Protocol.Core.Security
import IceNine.Protocol.Core.Patterns

namespace IceNine.Protocol

open List

-- Re-export from Security and Patterns for backward compatibility
-- Users importing Core get access to these types automatically

universe u

/-!
## Scheme Record

The Scheme bundles all algebraic and cryptographic parameters:
- Secret/Public modules connected by linear map A
- Commitment scheme for hiding values until reveal
- Hash function for Fiat-Shamir challenges
- Norm predicate for lattice signature security
-/
structure Scheme where
  -- Party identifiers (e.g., Nat or a finite type)
  PartyId   : Type u
  -- Messages to be signed (e.g., ByteArray)
  Message   : Type u
  -- Secret key space (e.g., short lattice vectors)
  Secret    : Type u
  -- Public key space (e.g., lattice points)
  Public    : Type u
  -- Challenge space from hash (e.g., small polynomials)
  Challenge : Type u
  -- Scalar ring for module operations
  Scalar    : Type u

  -- Algebraic structure: scalars form a semiring
  [scalarSemiring : Semiring Scalar]
  -- Secrets form an additive group (for share combination)
  [secretAdd    : AddCommGroup Secret]
  -- Public values form an additive group (for key aggregation)
  [publicAdd    : AddCommGroup Public]

  -- Module structures enable scalar multiplication
  [secretModule : Module Scalar Secret]
  [publicModule : Module Scalar Public]

  -- Challenges can scale secrets/publics (for z = y + c·s)
  [challengeSMulSecret : SMul Challenge Secret]
  [challengeSMulPublic : SMul Challenge Public]

  /-
  ## The Linear Map A

  The one-way linear map: pk = A(sk). Security relies on hardness of
  inverting A (SIS/LWE in lattice setting).

  ### Design Choice: Why No Explicit Error Term

  In Dilithium, the public key is t = As₁ + s₂ where s₂ is a small error term.
  This error term serves a specific purpose: making the public key
  indistinguishable from random under MLWE.

  We deliberately keep the abstract map A : S → P without an explicit error
  term for these reasons:

  1. **Abstraction boundary**: The error term is a key generation detail.
     Once the public key t is computed, signing and verification only need
     the linear relationship A(z) = A(y) + c·A(sk).

  2. **HighBits is an implementation detail**: Dilithium uses HighBits() to
     absorb c·s₂ during verification. This truncation can be encoded in:
     - The `hash` function (hash truncated w, not full w)
     - The `normOK` predicate (include HighBits consistency check)

  3. **Clean protocol logic**: The signing/verification math stays clean:
        z = y + c·sk
        A(z) - c·pk = A(y) = w
     The error handling lives in the concrete instantiation, not the abstract protocol.

  4. **Instantiation flexibility**: Different lattice schemes handle errors
     differently (Dilithium vs Falcon vs others). The abstract Scheme lets
     each instantiation encode its approach appropriately.

  For a Dilithium instantiation, define:
  - `A` maps the signing key s₁ (the public key t = As₁ + s₂ is precomputed)
  - `normOK` checks both ||z||∞ < γ₁ - β AND HighBits consistency
  - `hash` operates on HighBits(w) rather than full w

  Reference: Lyubashevsky et al., "CRYSTALS-Dilithium", TCHES 2018.
  -/
  A : Secret →ₗ[Scalar] Public

  /-
  ## Commitment Scheme

  We abstract the commitment scheme via `commit` and `commitBinding`. This models
  a computationally binding, perfectly hiding commitment scheme.

  ### Security Properties

  A commitment scheme has two security properties:

  1. **Binding**: Once committed, the committer cannot open to a different value.
     Formalized as: commit(x₁, o₁) = commit(x₂, o₂) → x₁ = x₂
     We include this as `commitBinding` in the Scheme structure.

  2. **Hiding**: The commitment reveals nothing about the committed value.
     Formalized as: ∀ x₁ x₂, {commit(x₁, o) : o ← random} ≈ {commit(x₂, o) : o ← random}
     (distributions are computationally/statistically indistinguishable)

  **IMPORTANT**: We only formalize binding, not hiding. Hiding is assumed but not
  enforced in the type system. The demo instances in `Instances.lean` do NOT
  satisfy hiding (they store the value in plaintext). This is acceptable because:
  - Protocol correctness proofs only need binding
  - Hiding is needed for security proofs (simulation-based arguments)
  - Formal hiding would require probabilistic reasoning infrastructure

  ### Concrete Instantiations

  | Scheme | Hiding | Binding | Assumption |
  |--------|--------|---------|------------|
  | Pedersen | Perfect | Computational | DLog hardness |
  | Hash-based H(x‖r) | Computational | Computational | ROM |
  | ElGamal-style | Perfect | Computational | DDH |

  **Design Choice**: We axiomatize binding rather than instantiating a concrete
  scheme (e.g., Pedersen, hash-based) because:
  1. The protocol correctness is independent of commitment instantiation
  2. Different deployment contexts may require different schemes
  3. Formal verification of concrete schemes would require additional crypto assumptions

  **Reference**: Halevi & Micali, "Practical and Provably-Secure Commitment Schemes
  from Collision-Free Hashing", CRYPTO 1996. Shows binding ↔ collision resistance.

  In practice, use Pedersen commitments (perfectly hiding, computationally binding
  under DLog) or hash-based commitments (computationally hiding/binding under ROM).
  -/

  -- Commitment scheme types
  Commitment : Type u
  Opening    : Type u
  -- Com(value, randomness) → commitment
  commit     : Public → Opening → Commitment

  -- Binding: can't open same commitment to different values.
  -- Prevents adversary from changing committed value after commit phase.
  -- This is the computational binding property - we axiomatize it here.
  --
  -- NOTE: Hiding is NOT formalized. See documentation above.
  -- Demo instances do NOT satisfy hiding - they are for correctness proofs only.
  commitBinding :
    ∀ {x₁ x₂ : Public} {o₁ o₂ : Opening},
      commit x₁ o₁ = commit x₂ o₂ → x₁ = x₂

  /-
  ## Hash Function (Random Oracle)

  The hash function is used for Fiat-Shamir transformation: converting interactive
  proofs to non-interactive by hashing the transcript to derive challenges.

  **Design Choice**: We model hash as a deterministic function with axiomatized
  collision resistance. This is the Random Oracle Model (ROM) - we assume the hash
  behaves like a random function that all parties can query.

  **Reference**: Bellare & Rogaway, "Random Oracles are Practical", CCS 1993.
  Also: Pointcheval & Stern, "Security Proofs for Signature Schemes", EUROCRYPT 1996.

  In practice, instantiate with SHA-3/SHAKE or domain-separated SHA-256.
  The ROM assumption is standard for Schnorr-style signatures.
  -/

  -- Collision resistance assumption (axiomatized for security proofs)
  -- In ROM, this holds with overwhelming probability.
  hashCollisionResistant : Prop

  /-
  ## Domain-Separated Hash Functions (FROST Pattern)

  Following FROST RFC, we use domain-separated hash functions for different purposes.
  Each hash is prefixed with a domain string to prevent cross-protocol attacks.

  | Domain | FROST Name | Purpose |
  |--------|------------|---------|
  | bindingFactor | H1 | Compute binding factors ρ_i |
  | challenge | H2 | Fiat-Shamir challenge c |
  | nonce | H3 | Nonce derivation |
  | message | H4 | Message pre-hashing |
  | commitmentList | H5 | Commitment list encoding |
  | dkg | HDKG | DKG proof of knowledge |
  | identifier | HID | Party ID derivation |

  **Security**: Domain separation ensures that a hash collision in one context
  cannot be exploited in another context.
  -/

  -- Domain-separated hash to scalar (for binding factors, PoK challenges, etc.)
  hashToScalar :
    ByteArray →                 -- domain prefix (e.g., "ice-nine-v1-rho")
    ByteArray →                 -- input data
    Scalar

  -- Domain-separated hash for DKG proof of knowledge challenge
  -- c = H_dkg(pid, pk_i, R) where R is the commitment
  hashDkg :
    PartyId →                   -- prover's identifier
    Public →                    -- prover's public key
    Public →                    -- commitment R = A(k)
    Scalar

  -- Fiat-Shamir hash: binds challenge to full transcript.
  -- Inputs: message, public key, signers, commitments, nonce sum.
  -- This is H2 (challenge) in FROST terminology.
  hash :
    Message →
    Public →                    -- global public key
    List PartyId →              -- participant set S
    List Commitment →           -- nonce commitments
    Public →                    -- aggregated nonce w = Σ w_i
    Challenge

  -- Optional: derive party identifier from arbitrary bytes
  -- Returns none if the derived value is zero (invalid identifier)
  deriveIdentifier : ByteArray → Option PartyId := fun _ => none

  -- Norm bound predicate for lattice security.
  -- Rejects signatures with large z to prevent leakage.
  normOK : Secret → Prop

  -- Decidability of normOK for runtime checking.
  -- Default: trivially decidable (True or compute-based).
  [normOKDecidable : DecidablePred normOK]

attribute [instance] Scheme.scalarSemiring Scheme.secretAdd Scheme.publicAdd

/-!
## Standard Constraint Aliases

These abbreviations reduce verbosity in function signatures. The Protocol modules
frequently require the same combinations of type class constraints on `S.PartyId`.

**Usage**: Replace verbose constraint lists with these aliases:
```lean
-- Before:
def foo (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] ...

-- After:
def foo (S : Scheme) [PartyIdHash S] [DecidableEq S.PartyId] ...
```

**Note**: These are `abbrev` not `class`, so they expand transparently.
-/

/-- Constraints for HashMap-keyed structures (MsgMap, NonceRegistry).
    Provides boolean equality and hashing for S.PartyId. -/
abbrev PartyIdHash (S : Scheme) := BEq S.PartyId × Hashable S.PartyId

/-- Extract BEq instance from PartyIdHash. -/
instance PartyIdHash.toBEq {S : Scheme} [h : PartyIdHash S] : BEq S.PartyId := h.1

/-- Extract Hashable instance from PartyIdHash. -/
instance PartyIdHash.toHashable {S : Scheme} [h : PartyIdHash S] : Hashable S.PartyId := h.2

/-- Full constraints for state operations: HashMap + decidable equality.
    Use when functions need both HashMap operations and if-then-else guards. -/
abbrev PartyIdState (S : Scheme) := PartyIdHash S × DecidableEq S.PartyId

/-- Extract PartyIdHash from PartyIdState. -/
instance PartyIdState.toHash {S : Scheme} [h : PartyIdState S] : PartyIdHash S := h.1

/-- Extract DecidableEq from PartyIdState. -/
instance PartyIdState.toDecidableEq {S : Scheme} [h : PartyIdState S] : DecidableEq S.PartyId := h.2

/-- Constraints for Lagrange coefficient computation.
    Requires field arithmetic and decidable equality on scalars. -/
abbrev ScalarField (S : Scheme) := Field S.Scalar × DecidableEq S.Scalar

/-- Extract Field instance from ScalarField. -/
instance ScalarField.toField {S : Scheme} [h : ScalarField S] : Field S.Scalar := h.1

/-- Extract DecidableEq instance from ScalarField. -/
instance ScalarField.toDecidableEq {S : Scheme} [h : ScalarField S] : DecidableEq S.Scalar := h.2

/-!
## Generic Share Verification

The pattern `A(secret) = expectedPublic` appears throughout the protocol:
- VSS share verification: A(s_ij) matches polynomial commitment
- Repair verification: A(repaired_sk) = known pk_i
- Refresh verification: A(refreshed_share) = updated pk_i
- DKG verification: A(sk_i) = pk_i

These functions centralize that pattern for consistency and reuse.
-/

/-- Verify that a secret value corresponds to an expected public value.
    This is the fundamental verification check: A(secret) = public.

    **Usage**: All share verification reduces to this check.
    - VSS: verify share against commitment evaluation
    - Repair: verify reconstructed share against known public share
    - Refresh: verify updated share against updated public share -/
def verifySecretPublic (S : Scheme) (secret : S.Secret) (expectedPublic : S.Public) : Prop :=
  S.A secret = expectedPublic

/-- Boolean version of verifySecretPublic for runtime checks. -/
def verifySecretPublicBool (S : Scheme) [DecidableEq S.Public]
    (secret : S.Secret) (expectedPublic : S.Public) : Bool :=
  S.A secret = expectedPublic

/-- Verify a secret share against its public share.
    Wrapper with clearer naming for share-specific verification. -/
abbrev verifyShare (S : Scheme) := verifySecretPublic S

/-- Boolean share verification. -/
abbrev verifyShareBool (S : Scheme) [DecidableEq S.Public] := verifySecretPublicBool S

/-- Verify that a commitment opens to an expected value.
    Used in commit-reveal protocols (DKG, refresh, repair).

    **Pattern**: After reveal, check `commit(value, opening) = commitment`. -/
def verifyCommitmentOpening (S : Scheme) [DecidableEq S.Commitment]
    (value : S.Public) (opening : S.Opening) (expectedCommit : S.Commitment) : Bool :=
  S.commit value opening = expectedCommit

/-- Verify commitment to A(secret) for protocols that commit to public images.
    Used in refresh and repair where we commit to A(mask) or A(contribution). -/
def verifySecretCommitment (S : Scheme) [DecidableEq S.Commitment]
    (secret : S.Secret) (opening : S.Opening) (expectedCommit : S.Commitment) : Bool :=
  S.commit (S.A secret) opening = expectedCommit

/-!
## Scheme-Specific HasSender Instances

The HasSender typeclass is defined in Patterns.lean.
Here we provide instances for Scheme-dependent message types.
-/

-- Standard instances for protocol messages (message types defined later in this file)
-- These are forward-declared and defined after the message type definitions

/-!
## Commit Verification Typeclass

Typeclass for verifiable commit-reveal pairs, defined here because
it needs Scheme for the verification function.
-/

/-- Typeclass for commit messages that can be verified against reveals.
    Enables generic commit-reveal verification. -/
class CommitVerifiable (CommitMsg RevealMsg : Type*) (S : Scheme) where
  /-- Verify that a reveal correctly opens a commit -/
  verifyOpening : S → CommitMsg → RevealMsg → Bool

/-!
## Domain Separation Constants

Following FROST, we use domain-separated hash functions. Each domain has a
unique prefix string to prevent cross-protocol attacks.

**Protocol version**: Prefix includes "v1" so future versions can change domains.
-/

-- Domain separation strings for Ice-Nine protocol
namespace HashDomain
  /-- Binding factor computation (FROST H1) -/
  def bindingFactor : ByteArray := "ice-nine-v1-rho".toUTF8
  /-- Fiat-Shamir challenge (FROST H2) -/
  def challenge : ByteArray := "ice-nine-v1-chal".toUTF8
  /-- Nonce derivation (FROST H3) -/
  def nonce : ByteArray := "ice-nine-v1-nonce".toUTF8
  /-- Message pre-hashing (FROST H4) -/
  def message : ByteArray := "ice-nine-v1-msg".toUTF8
  /-- Commitment list encoding (FROST H5) -/
  def commitmentList : ByteArray := "ice-nine-v1-com".toUTF8
  /-- DKG proof of knowledge (FROST HDKG) -/
  def dkg : ByteArray := "ice-nine-v1-dkg".toUTF8
  /-- Party identifier derivation (FROST HID) -/
  def identifier : ByteArray := "ice-nine-v1-id".toUTF8
end HashDomain

/-!
## Instance Constraint Patterns

Protocol modules use consistent instance requirements. This section documents
the standard patterns to ensure consistency across the codebase.

### HashMap-Based Structures (MsgMap, NonceRegistry)

For `Std.HashMap`-based structures:
```
[BEq S.PartyId] [Hashable S.PartyId]
```

These are required for HashMap key operations. Always use together.

### Decidable Equality (conditionals, find, filter)

For if-then-else, `List.find?`, `List.filter`:
```
[DecidableEq S.PartyId]
```

This is Prop-valued equality with a decision procedure. Required when
comparing party IDs in conditional expressions.

### Field Arithmetic (Lagrange coefficients)

For Lagrange interpolation:
```
[Field S.Scalar] [DecidableEq S.Scalar]
```

Field is required for division in λ_i = Π x_j / (x_j - x_i).
DecidableEq is needed to check for degenerate cases.

### Combined Pattern

Functions using both HashMap and conditionals need all three:
```
[BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
```

**Note**: `BEq` and `DecidableEq` are distinct:
- `BEq`: Boolean equality for HashMap (computational)
- `DecidableEq`: Prop equality with decision (for proofs)

In practice, if you have `DecidableEq`, you can derive `BEq`:
```lean
instance [DecidableEq α] : BEq α := ⟨fun a b => decide (a = b)⟩
```
-/

/-!
## Identifier Derivation

Party identifiers can be derived from arbitrary data (usernames, emails, etc.)
using domain-separated hashing. This is FROST's HID function.
-/

/-- Derive a party identifier from a byte string.
    Uses the scheme's deriveIdentifier if provided, otherwise returns none.

    **Security**: The derived identifier must be non-zero. Implementations
    should reject zero values (which could cause issues in Lagrange interpolation). -/
def Scheme.deriveId (S : Scheme) (data : ByteArray) : Option S.PartyId :=
  S.deriveIdentifier data
attribute [instance] Scheme.secretModule Scheme.publicModule
attribute [instance] Scheme.challengeSMulSecret Scheme.challengeSMulPublic
attribute [instance] Scheme.normOKDecidable

/-!
## Randomness Requirements

This protocol requires cryptographically secure randomness (CSPRNG) at several points.
**All randomness MUST be sampled from a cryptographically secure source** (e.g., `/dev/urandom`,
`getrandom()`, `CryptGenRandom`, or equivalent OS facility).

| Value | Generation | Security Impact |
|-------|------------|-----------------|
| `sk_i` | DKG: each party samples own share | Secret key - obvious |
| `y_i` | Signing: ephemeral nonce | Nonce reuse = key recovery |
| `Opening` | Commitments: randomness for hiding | Predictable = hiding breaks |
| `randomCoeffs` | VSS: polynomial coefficients | Bias = share correlation |
| `masks` | Refresh/Rerandomize: zero-sum masks | Bias = refresh leakage |

### Nonce Catastrophe Warning

**CRITICAL**: Reusing a nonce `y_i` across two signing sessions with the same key
immediately leaks the secret share `sk_i`:

    z₁ = y + c₁·sk
    z₂ = y + c₂·sk
    ⟹  sk = (z₁ - z₂) / (c₁ - c₂)

The `SignSession` API is designed to prevent this by coupling nonce sampling with
session creation. Never implement signing without using the session API.

### Implementation Guidance

1. **OS-level CSPRNG**: Use `getrandom(2)` on Linux, `arc4random(3)` on BSD/macOS,
   `BCryptGenRandom` on Windows. Do NOT use `rand()`, `random()`, or PRNGs.

2. **Nonce derivation** (alternative): RFC 6979 deterministic nonces can prevent
   catastrophic reuse but require careful implementation. If using deterministic
   nonces, the derivation MUST include the message, key, and a counter.

3. **Rejection sampling**: The Dilithium-style signing loop requires fresh `y_i`
   for each retry. Never reuse a rejected nonce.

4. **Entropy at startup**: Ensure sufficient entropy before first key/nonce generation.
   Block if entropy pool is depleted (`GRND_RANDOM` flag on Linux).
-/

/-!
## Naming Conventions

This codebase uses semantically distinct names for party collections:

| Name | Meaning | Usage |
|------|---------|-------|
| `Sset` | Signer set | Specific signers chosen for a signing session |
| `active` | Active parties | Parties currently participating in a protocol phase |
| `parties` / `allParties` | Complete party list | Full set for Lagrange interpolation or DKG |
| `validParties` | Verified parties | Parties that passed a verification check |
| `helpers` | Helper parties | Parties assisting in repair operations |
| `threshold` / `t` | Threshold value | Minimum parties needed for reconstruction |

These distinctions are intentional - a signer set (`Sset`) is a specific subset
chosen for one signing session, while `active` tracks dynamic participation,
and `parties` is the complete enumeration for coefficient computation.
-/

/-!
## Key and Message Types

After DKG, each party holds a KeyShare. During DKG, parties exchange
commit and reveal messages to jointly generate the threshold key.
-/

/-!
## Linear Security Wrappers

Note: Zeroizable, ConstantTimeEq, SecretBox, and NonceBox are imported from Security.lean.

These wrappers enforce single-use discipline for sensitive protocol values.
While Lean doesn't have true linear types, these wrappers use private constructors
and module-scoped access to make misuse visible and intentional.

**Design Pattern**: Each wrapper has:
1. Private constructor (`private mk`) - prevents arbitrary creation
2. Private value field - prevents direct access outside module
3. Public creation function - controlled entry point
4. Consumption functions - defined in the module that needs them

This pattern ensures that using these values requires explicit acknowledgment
of their sensitive, single-use nature.
-/

/-- A mask value for share refresh that must be applied exactly once.
    Reusing masks breaks the zero-sum invariant.

    **Security**: Refresh masks must sum to zero across all parties.
    If a mask is applied twice, or not applied, the sum property fails
    and the global secret changes.

    **Usage**:
    1. Create via `LinearMask.create` with freshly sampled randomness
    2. Apply via refresh protocol functions (consumes the mask conceptually)
    3. Never store or duplicate - treat as single-use -/
structure LinearMask (S : Scheme) where
  private mk ::
  /-- The party this mask belongs to -/
  private partyId : S.PartyId
  /-- The secret mask value -/
  private maskValue : S.Secret
  /-- Public commitment A(mask) for verification -/
  private publicImage : S.Public

/-- Create a linear mask from freshly sampled randomness.
    **CRITICAL**: The mask value must be fresh from CSPRNG. -/
def LinearMask.create (S : Scheme) (pid : S.PartyId) (mask : S.Secret) : LinearMask S :=
  { partyId := pid, maskValue := mask, publicImage := S.A mask }

/-- Get the party ID (safe - not secret). -/
def LinearMask.pid {S : Scheme} (m : LinearMask S) : S.PartyId := m.partyId

/-- Get the public image A(mask) for verification (safe - not secret). -/
def LinearMask.public {S : Scheme} (m : LinearMask S) : S.Public := m.publicImage

/-- LinearMask requires zeroization. -/
instance {S : Scheme} : Zeroizable (LinearMask S) where
  needsZeroization := true

/-- LinearMask requires constant-time equality. -/
instance {S : Scheme} : ConstantTimeEq (LinearMask S) where
  requiresConstantTime := true

/-- Proof that a linear mask was consumed. -/
structure MaskConsumed (S : Scheme) where
  private mk ::
  /-- Party whose mask was consumed -/
  forParty : S.PartyId

/-- A repair delta that must be used exactly once.
    Using a delta twice corrupts the reconstructed share.

    **Security**: Repair deltas are Lagrange-weighted secret shares.
    Each delta contributes to reconstructing the lost share:
      sk_i = Σ_j λ_j · sk_j
    Using a delta twice would add it to the sum twice.

    **Usage**:
    1. Create via `LinearDelta.create` in helper contribution
    2. Send to requester (single recipient)
    3. Aggregate exactly once during repair -/
structure LinearDelta (S : Scheme) where
  private mk ::
  /-- The helper party who contributed this delta -/
  private senderId : S.PartyId
  /-- The requester this delta is for -/
  private targetId : S.PartyId
  /-- The secret delta value (λ_j · sk_j) -/
  private deltaValue : S.Secret

/-- Create a linear delta for repair contribution.
    **CRITICAL**: The delta should be the Lagrange-weighted share. -/
def LinearDelta.create (S : Scheme) (sender target : S.PartyId) (delta : S.Secret) : LinearDelta S :=
  { senderId := sender, targetId := target, deltaValue := delta }

/-- Get the sender ID (safe - not secret). -/
def LinearDelta.sender {S : Scheme} (d : LinearDelta S) : S.PartyId := d.senderId

/-- Get the target ID (safe - not secret). -/
def LinearDelta.target {S : Scheme} (d : LinearDelta S) : S.PartyId := d.targetId

/-- LinearDelta requires zeroization. -/
instance {S : Scheme} : Zeroizable (LinearDelta S) where
  needsZeroization := true

/-- LinearDelta requires constant-time equality. -/
instance {S : Scheme} : ConstantTimeEq (LinearDelta S) where
  requiresConstantTime := true

/-- Proof that a linear delta was consumed. -/
structure DeltaConsumed (S : Scheme) where
  private mk ::
  /-- Helper whose delta was consumed -/
  fromHelper : S.PartyId

/-- A commitment opening that should be used exactly once.
    Reusing an opening with different values enables equivocation.

    **Security**: Commitment openings are the randomness that makes
    commitments hiding. If the same opening is used with different
    values, an adversary could potentially equivocate (open the same
    commitment to different values).

    **Usage**:
    1. Create via `LinearOpening.fresh` with CSPRNG randomness
    2. Use exactly once in commit-reveal protocol
    3. Discard after reveal phase -/
structure LinearOpening (S : Scheme) where
  private mk ::
  /-- The secret opening value -/
  private openingValue : S.Opening
  /-- Whether this opening has been used (for runtime check) -/
  private used : Bool := false

/-- Create a fresh linear opening from sampled randomness.
    **CRITICAL**: The opening must be fresh from CSPRNG. -/
def LinearOpening.fresh (S : Scheme) (opening : S.Opening) : LinearOpening S :=
  { openingValue := opening, used := false }

/-- Check if opening has been used (for defensive runtime checks). -/
def LinearOpening.isUsed {S : Scheme} (o : LinearOpening S) : Bool := o.used

/-- LinearOpening requires zeroization. -/
instance {S : Scheme} : Zeroizable (LinearOpening S) where
  needsZeroization := true

/-- Proof that a linear opening was consumed. -/
structure OpeningConsumed (S : Scheme) where
  private mk ::
  /-- Marker that opening was consumed -/
  consumed : Unit := ()

/-!
## Linear Type Access Functions

These functions provide controlled access to the secret values inside
linear wrappers. They are defined here in Core so that protocol modules
can use them, but the private constructors prevent arbitrary creation.
-/

/-- Extract mask value for application. Returns value and consumption proof.
    **Security**: Only call this when actually applying the mask. -/
def LinearMask.consume {S : Scheme} (m : LinearMask S) : S.Secret × MaskConsumed S :=
  (m.maskValue, { forParty := m.partyId })

/-- Extract delta value for aggregation. Returns value and consumption proof.
    **Security**: Only call this when actually aggregating the delta. -/
def LinearDelta.consume {S : Scheme} (d : LinearDelta S) : S.Secret × DeltaConsumed S :=
  (d.deltaValue, { fromHelper := d.senderId })

/-- Extract opening value for commitment. Returns value and consumption proof.
    **Security**: Only call this when actually creating/opening a commitment. -/
def LinearOpening.consume {S : Scheme} (o : LinearOpening S) : S.Opening × OpeningConsumed S :=
  (o.openingValue, { consumed := () })

/-- A party's credential after DKG completes. Contains the secret share
    sk_i, public share pk_i = A(sk_i), and global key pk = Σ pk_i.

    **Security Note**: The `sk_i` field is wrapped in SecretBox to discourage
    accidental exposure. Use `share.secret` accessor when computation requires it.
    This creates a clear audit trail for secret access.
    Never print, log, or serialize the secret share directly. -/
structure KeyShare (S : Scheme) where
  pid  : S.PartyId           -- this party's identifier
  sk_i : SecretBox S.Secret  -- secret share (never shared) - wrapped for safety
  pk_i : S.Public            -- public share = A(sk_i)
  pk   : S.Public            -- global public key = Σ pk_j

/-- Create KeyShare from unwrapped secret (convenience function).
    Use this during DKG when creating shares. -/
def KeyShare.create (S : Scheme) (pid : S.PartyId) (sk : S.Secret) (pk_i pk : S.Public)
    : KeyShare S :=
  { pid := pid, sk_i := ⟨sk⟩, pk_i := pk_i, pk := pk }

/-- Get the unwrapped secret share for computation.
    **Security**: Only use when the secret is needed for cryptographic operations. -/
def KeyShare.secret {S : Scheme} (share : KeyShare S) : S.Secret :=
  share.sk_i.val


/-!
## Proof of Knowledge (FROST Pattern)

Following FROST, DKG includes a proof of knowledge (PoK) to prevent rogue-key attacks.
Without PoK, an adversary could choose their public key as a function of honest parties'
keys, potentially biasing the aggregate key.

The PoK is a Schnorr-style proof: given pk_i = A(sk_i), prove knowledge of sk_i.
1. Prover samples random k, computes R = A(k)
2. Challenge c = H_dkg(pid, pk_i, R)
3. Response μ = k + c·sk_i
4. Verifier checks: A(μ) = R + c·pk_i

**Security**: This prevents rogue-key attacks because the adversary must know sk_i
to produce a valid proof. They cannot adaptively choose pk_i after seeing others' keys.

Reference: FROST RFC Section 5.1, Komlo & Goldberg "FROST" (2020)
-/

/-- Proof of knowledge for DKG: proves knowledge of secret corresponding to public key.
    Schnorr-style: given pk = A(sk), prove knowledge of sk. -/
structure ProofOfKnowledge (S : Scheme) where
  /-- Commitment R = A(k) for random nonce k -/
  commitment : S.Public
  /-- Response μ = k + c·sk where c = H_dkg(pid, pk, R) -/
  response   : S.Secret

/-- DKG round 1: party broadcasts commitment to its public share.
    Hiding pk_i until all parties commit prevents adaptive attacks.
    Includes proof of knowledge to prevent rogue-key attacks. -/
structure DkgCommitMsg (S : Scheme) where
  sender   : S.PartyId
  commitPk : S.Commitment
  /-- Proof of knowledge of secret corresponding to public share -/
  pok      : ProofOfKnowledge S


/-- DKG round 2: party reveals pk_i and opening to verify commitment.
    Others check: commit(pk_i, opening) = commitPk from round 1. -/
structure DkgRevealMsg (S : Scheme) where
  sender  : S.PartyId
  pk_i    : S.Public
  opening : S.Opening


/-- Party's local state during DKG. The secret sk_i is sampled locally
    and never transmitted. Only the commitment/reveal are broadcast. -/
structure DkgLocalState (S : Scheme) where
  pid    : S.PartyId
  sk_i   : S.Secret     -- locally sampled secret share
  pk_i   : S.Public     -- pk_i = A(sk_i)
  openPk : S.Opening    -- randomness for commitment


/-!
## External Context

External protocols can attach context to signing messages.
This enables binding signatures to external consensus instances, operations, and
evidence propagation without coupling Ice Nine to specific protocols.

Defined in Core to be available to both Core (SignShareMsg) and SignTypes.
-/

/-- External context that can be attached to signing messages.
    Enables protocols like Aura to bind signatures to their domain.

    All fields are optional - Ice Nine's core signing works without them.
    External protocols populate the fields they need. -/
structure ExternalContext where
  /-- External consensus/session identifier (e.g., Aura's `cid`) -/
  consensusId : Option ByteArray := none
  /-- Result identifier (e.g., H(operation, prestate) for Aura) -/
  resultId : Option ByteArray := none
  /-- Prestate hash for validation -/
  prestateHash : Option ByteArray := none
  /-- Opaque evidence delta for CRDT propagation -/
  evidenceDelta : Option ByteArray := none
  deriving Repr

/-- Empty external context (default for standalone use). -/
def ExternalContext.empty : ExternalContext := {}

/-- Check if context has any fields set. -/
def ExternalContext.isEmpty (ctx : ExternalContext) : Bool :=
  ctx.consensusId.isNone && ctx.resultId.isNone &&
  ctx.prestateHash.isNone && ctx.evidenceDelta.isNone

/-- Merge two contexts, preferring values from the first.
    Used when aggregating shares with potentially different evidence deltas. -/
def ExternalContext.merge (a b : ExternalContext) : ExternalContext :=
  { consensusId := a.consensusId <|> b.consensusId
    resultId := a.resultId <|> b.resultId
    prestateHash := a.prestateHash <|> b.prestateHash
    evidenceDelta := a.evidenceDelta <|> b.evidenceDelta }

/-- Check if two contexts are consistent (same non-none values).
    Used for validating shares reference the same consensus instance. -/
def ExternalContext.isConsistent [BEq ByteArray] (a b : ExternalContext) : Bool :=
  let check := fun (x y : Option ByteArray) =>
    match x, y with
    | some vx, some vy => vx == vy
    | _, _ => true  -- one or both none is consistent
  check a.consensusId b.consensusId &&
  check a.resultId b.resultId &&
  check a.prestateHash b.prestateHash
  -- Note: evidenceDelta is not checked - different parties may have different deltas

/-!
## Evidence Carrier Typeclass

Typeclass for messages that can carry CRDT evidence deltas.
This enables protocols like Aura to piggyback evidence on signing messages
without Ice Nine needing to understand the evidence format.
-/

/-- Typeclass for messages that can carry CRDT evidence deltas.
    Enables protocols like Aura to piggyback evidence on signing messages.

    **Usage pattern**:
    1. Before sending: `attachEvidence msg myDelta`
    2. On receive: `extractEvidence msg` to get delta for merge
    3. Query: `hasEvidence msg` to check if evidence attached -/
class EvidenceCarrier (M : Type*) where
  /-- Attach evidence delta to a message -/
  attachEvidence : M → ByteArray → M
  /-- Extract evidence delta from a message -/
  extractEvidence : M → Option ByteArray
  /-- Check if message has evidence attached -/
  hasEvidence : M → Bool := fun m => (extractEvidence m).isSome

/-- Convenience: attach evidence only if some -/
def EvidenceCarrier.attachOpt [EvidenceCarrier M] (m : M) (evid : Option ByteArray) : M :=
  match evid with
  | some e => EvidenceCarrier.attachEvidence m e
  | none => m

/-!
## Signing Message Types

These are placed in Core to break circular dependencies between Phase and Sign.
-/

/-- Round 2 signing message: partial signature z_i = y_i + c·sk_i.
    Ephemeral nonce y_i masks the secret share contribution. -/
structure SignShareMsg (S : Scheme) where
  sender  : S.PartyId
  session : Nat
  z_i     : S.Secret
  /-- External context for protocol integration (optional) -/
  context : ExternalContext := {}

/-- EvidenceCarrier instance for SignShareMsg. -/
instance (S : Scheme) : EvidenceCarrier (SignShareMsg S) where
  attachEvidence := fun msg evid =>
    { msg with context := { msg.context with evidenceDelta := some evid } }
  extractEvidence := fun msg => msg.context.evidenceDelta


end IceNine.Protocol
