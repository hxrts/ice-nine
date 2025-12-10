/-
# Secret Wrappers (Lightweight Linear Discipline)

Wrapper types that discourage accidental duplication or exposure of
sensitive data. Not true linear types, but signals intent and makes
misuse more visible in code review.

Usage:
- Wrap secrets before storing: SecretBox.mk sk
- Unwrap only when computing: box.val
- Avoid pattern-matching on Box types in public modules
-/

namespace IceNine.Protocol

/-!
## Secret Box

Wraps secret key material. Discourages copying or pattern-matching.
Use .val accessor explicitly when computation requires the value.
-/

/-- Wrapper for secret keys to discourage accidental exposure.
    Unwrap with .val only when computation requires it. -/
structure SecretBox (α : Type) where
  val : α
deriving Repr

/-!
## Nonce Box

Wraps ephemeral nonces. Critical: nonces must NEVER be reused.
Wrapper makes nonce handling more visible in code.
-/

/-- Wrapper for nonces to highlight their ephemeral nature.
    Nonce reuse is catastrophic: treat these as single-use. -/
structure NonceBox (α : Type) where
  val : α
deriving Repr

end IceNine.Protocol
