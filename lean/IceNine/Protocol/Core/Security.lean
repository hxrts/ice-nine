/-
# Security Markers and Wrappers

This module contains Scheme-independent security-related types and markers:
- Side-channel considerations (documentation)
- Memory zeroization markers (`Zeroizable`, `ConstantTimeEq`)
- Generic secret wrappers (`SecretBox`, `NonceBox`)

Scheme-dependent security types (linear wrappers) are in Core.lean.

These types document security requirements for production implementations
and enforce discipline around sensitive values.
-/

import Mathlib

namespace IceNine.Protocol

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
4. `verifyShareBool` (Protocol/DKG/Feldman.lean) - Comparison may short-circuit

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

/-!
## SecretBox

Wrapper for secret keys to discourage accidental exposure.
-/

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

end IceNine.Protocol
