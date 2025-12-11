/-
# Secret Wrappers (Lightweight Linear Discipline)

Wrapper types that discourage accidental duplication or exposure of
sensitive data. Not true linear types, but signals intent and makes
misuse more visible in code review.

**Note**: SecretBox is now defined in Core.lean where KeyShare uses it.
This file is retained for NonceBox and any additional secret wrappers.

Usage:
- Wrap secrets before storing: SecretBox.mk sk (in Core.lean)
- Unwrap only when computing: box.val
- Avoid pattern-matching on Box types in public modules
-/

import IceNine.Protocol.Core

namespace IceNine.Protocol

/-!
## Nonce Box

Wraps ephemeral nonces. Critical: nonces must NEVER be reused.
Wrapper makes nonce handling more visible in code.
-/

/-- Wrapper for nonces to highlight their ephemeral nature.
    Nonce reuse is catastrophic: treat these as single-use. -/
structure NonceBox (α : Type*) where
  private mk ::
  val : α

/-- Create a NonceBox from a fresh nonce.
    **Security**: The nonce MUST be freshly sampled from a CSPRNG. -/
def NonceBox.fresh {α : Type*} (nonce : α) : NonceBox α := ⟨nonce⟩

end IceNine.Protocol
