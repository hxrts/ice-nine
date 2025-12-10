/-
# Secret wrappers to discourage duplication in public data

We wrap secrets/nonces so they are not pattern-matched in public code. This is
lightweight (not a true linear type) but signals intent and reduces accidental
leakage.
-/

namespace IceNine.Protocol

structure SecretBox (α : Type) where
  val : α

structure NonceBox (α : Type) where
  val : α

end IceNine.Protocol
