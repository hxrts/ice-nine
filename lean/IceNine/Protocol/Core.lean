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
- `StateProduct.lean` (product semilattice)
- `PhaseMerge.lean` (composite CRDT state)
- `ThresholdMerge.lean` (threshold-aware merge)

**Serialization**:
- `Serialize.lean` (wire format)
-/

import Mathlib
import IceNine.Crypto

namespace IceNine.Protocol

open List

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

  -- The one-way linear map: pk = A(sk). Security relies on
  -- hardness of inverting A (SIS/LWE in lattice setting).
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
## Side-Channel Considerations

This formal specification does NOT address side-channel attacks. Production implementations
MUST consider the following timing and power analysis vulnerabilities:

### Data-Dependent Timing

| Operation | Risk | Mitigation |
|-----------|------|------------|
| Lagrange coefficient computation | Division timing varies with operands | Montgomery multiplication, constant-time inversion |
| Polynomial evaluation | Branch on coefficient values | Constant-time multiply-accumulate |
| Rejection sampling | Loop count leaks norm info | Add dummy iterations, constant-time norm check |
| Secret comparison | Early-exit on mismatch | Constant-time comparison (e.g., `crypto_verify_32`) |

### Memory Access Patterns

- **Cache timing**: Table lookups indexed by secret values leak through cache timing
- **Branch prediction**: Secret-dependent branches can be observed via Spectre-like attacks
- **Memory allocation**: Variable-size allocations may leak secret sizes

### Flagged Functions

The following functions in this codebase have data-dependent behavior that MUST be
replaced with constant-time implementations in production:

1. `lagrangeCoefficient` (Protocol/RepairCoord.lean) - Division varies with inputs
2. `allCoeffsAtZero` (Protocol/Lagrange.lean) - Loop over party list
3. `vecInfNorm` (Norms.lean) - Max computation has secret-dependent comparisons
4. `verifyShareBool` (Protocol/VSSCore.lean) - Comparison may short-circuit

### Recommendations

1. Use **constant-time primitives** from validated libraries (e.g., libsodium, HACL*)
2. Compile with **security hardening flags** (`-fstack-protector-strong`, `-D_FORTIFY_SOURCE=2`)
3. Consider **hardware isolation** (SGX, TrustZone) for secret key operations
4. Perform **side-channel audits** before deployment (differential power analysis, timing measurements)
5. Use **blinding techniques** where applicable (randomize intermediate values)
-/

/-!
## Memory Zeroization

Sensitive data MUST be securely erased from memory after use. Language runtime garbage
collectors and compiler optimizations may prevent naive zeroing from working.

### Sensitive Values Requiring Zeroization

| Type | Example | When to Zeroize |
|------|---------|-----------------|
| `SecretBox` | `KeyShare.sk_i` | After signing session completes |
| `y_i` | Ephemeral nonce | Immediately after computing `z_i` |
| `Opening` | Commitment randomness | After reveal phase |
| Intermediate `z_i` | Partial signature | After aggregation |
| Lagrange-weighted contributions | Repair deltas | After aggregation |

### Implementation Patterns

1. **Volatile writes**: Use `memset_s` or `explicit_bzero` which compilers cannot optimize away
2. **Secure allocators**: Use `mlock()` to prevent swapping secrets to disk
3. **RAII wrappers**: Implement `Drop`/destructor that zeroizes (SecretBox pattern)
4. **Memory barriers**: Insert barriers to prevent reordering around zeroization

### Platform-Specific APIs

| Platform | Secure Zeroize Function |
|----------|------------------------|
| C11+ | `memset_s(ptr, size, 0, size)` |
| POSIX | `explicit_bzero(ptr, size)` |
| Windows | `SecureZeroMemory(ptr, size)` |
| Rust | `zeroize` crate |
| Lean | (runtime-dependent, may need FFI) |

**Note**: The Lean runtime does not provide memory zeroization. For production use,
secret operations should be performed via FFI to a constant-time library.
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
## Zeroization Marker

Types containing sensitive data should implement `Zeroizable` to indicate
they require secure memory erasure after use. This is a marker typeclass
for documentation and Rust FFI - Lean cannot directly control memory.

**Implementation Requirements** (for Rust/C FFI):
1. Use `zeroize` crate or equivalent for secure erasure
2. Implement `Drop` trait to auto-zeroize on scope exit
3. Use `mlock()` to prevent swapping secrets to disk
4. Add memory barriers around zeroization
-/

/-- Marker typeclass for types requiring secure memory zeroization.
    Implementations should provide actual zeroization via FFI. -/
class Zeroizable (α : Type*) where
  /-- Marker that this type needs zeroization (implementation via FFI) -/
  needsZeroization : Bool := true

/-- Marker typeclass for types requiring constant-time equality comparison.
    Equality operations on these types MUST NOT have data-dependent timing.

    **Implementation Requirements** (for Rust/C FFI):
    1. Use constant-time comparison (e.g., `subtle::ConstantTimeEq` in Rust)
    2. Never use early-exit equality (like `==` on byte arrays)
    3. Process all bytes regardless of mismatch position
    4. Avoid compiler optimizations that reintroduce timing leaks

    **Types requiring constant-time equality**:
    - Secret keys and shares
    - Nonces and ephemeral values
    - Challenges and responses
    - Any value derived from secrets -/
class ConstantTimeEq (α : Type*) where
  /-- Marker that equality comparison must be constant-time -/
  requiresConstantTime : Bool := true

/-- Wrapper for secret keys to discourage accidental exposure.
    Unwrap with .val only when computation requires it.

    **Security Note**: This is a lightweight discipline, not true linear types.
    Code that pattern-matches on SecretBox must explicitly acknowledge it is
    handling secret material. Never print, log, or serialize SecretBox contents.

    **Zeroization**: SecretBox contents MUST be zeroized after use in production.
    Implement via FFI to zeroize crate in Rust. -/
structure SecretBox (α : Type*) where
  private mk ::
  val : α

/-- Wrap a secret value in a SecretBox.
    **Security**: The secret value should have been generated securely. -/
def SecretBox.wrap {α : Type*} (secret : α) : SecretBox α := ⟨secret⟩

/-- SecretBox requires zeroization. -/
instance {α : Type*} : Zeroizable (SecretBox α) where
  needsZeroization := true

/-- SecretBox requires constant-time equality. -/
instance {α : Type*} : ConstantTimeEq (SecretBox α) where
  requiresConstantTime := true

/-!
## Nonce Box

Wrapper for ephemeral nonces. Critical: nonces must NEVER be reused.
The wrapper makes nonce handling more visible in code.
-/

/-- Wrapper for nonces to highlight their ephemeral nature.
    Nonce reuse is catastrophic: treat these as single-use.

    **Security Note**: Reusing a nonce across signing sessions allows
    trivial secret key recovery. See Randomness Requirements section. -/
structure NonceBox (α : Type*) where
  private mk ::
  val : α

/-- Create a NonceBox from a fresh nonce.
    **Security**: The nonce MUST be freshly sampled from a CSPRNG. -/
def NonceBox.fresh {α : Type*} (nonce : α) : NonceBox α := ⟨nonce⟩

/-- NonceBox requires zeroization. -/
instance {α : Type*} : Zeroizable (NonceBox α) where
  needsZeroization := true

/-- NonceBox requires constant-time equality. -/
instance {α : Type*} : ConstantTimeEq (NonceBox α) where
  requiresConstantTime := true

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
## Signing Message Types

These are placed in Core to break circular dependencies between Phase and Sign.
-/

/-- Round 2 signing message: partial signature z_i = y_i + c·sk_i.
    Ephemeral nonce y_i masks the secret share contribution. -/
structure SignShareMsg (S : Scheme) where
  sender  : S.PartyId
  session : Nat
  z_i     : S.Secret


end IceNine.Protocol
