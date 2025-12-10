/-
# Protocol Core

Core algebraic definitions for the Ice Nine threshold signature protocol.
Defines the abstract Scheme record and basic message types for DKG.
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

  -- Fiat-Shamir hash: binds challenge to full transcript.
  -- Inputs: message, public key, signers, commitments, nonce sum.
  hash :
    Message →
    Public →                    -- global public key
    List PartyId →              -- participant set S
    List Commitment →           -- nonce commitments
    Public →                    -- aggregated nonce w = Σ w_i
    Challenge

  -- Norm bound predicate for lattice security.
  -- Rejects signatures with large z to prevent leakage.
  normOK : Secret → Prop

  -- Decidability of normOK for runtime checking.
  -- Default: trivially decidable (True or compute-based).
  [normOKDecidable : DecidablePred normOK]

attribute [instance] Scheme.scalarSemiring Scheme.secretAdd Scheme.publicAdd
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
session creation. **Never implement signing without using the session API.**

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

/-- Wrapper for secret keys to discourage accidental exposure.
    Unwrap with .val only when computation requires it.

    **Security Note**: This is a lightweight discipline, not true linear types.
    Code that pattern-matches on SecretBox must explicitly acknowledge it is
    handling secret material. Never print, log, or serialize SecretBox contents. -/
structure SecretBox (α : Type*) where
  private mk ::
  val : α

/-- A party's credential after DKG completes. Contains the secret share
    sk_i, public share pk_i = A(sk_i), and global key pk = Σ pk_i.

    **Security Note**: The `sk_i` field is wrapped in SecretBox to discourage
    accidental exposure. Access via `share.sk_i.val` when computation requires it.
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


/-- DKG round 1: party broadcasts commitment to its public share.
    Hiding pk_i until all parties commit prevents adaptive attacks. -/
structure DkgCommitMsg (S : Scheme) where
  sender   : S.PartyId
  commitPk : S.Commitment


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
