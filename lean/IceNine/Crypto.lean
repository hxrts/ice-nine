/-
# Cryptographic Primitives

Definitions and properties of cryptographic primitives used in the protocol.
-/

import Mathlib.Data.ByteArray
import Mathlib.Data.Fintype.Basic

namespace IceNine.Crypto

/-- A cryptographic key represented as a byte array -/
structure Key where
  bytes : ByteArray
  deriving Repr, DecidableEq

/-- A cryptographic signature -/
structure Signature where
  bytes : ByteArray
  deriving Repr, DecidableEq

/-- A hash digest -/
structure Hash where
  bytes : ByteArray
  deriving Repr, DecidableEq

/-- Abstract signature scheme -/
class SignatureScheme (KeyPair : Type) where
  /-- Generate a key pair -/
  keygen : IO KeyPair
  /-- Sign a message -/
  sign : KeyPair → ByteArray → Signature
  /-- Verify a signature -/
  verify : Key → ByteArray → Signature → Bool
  /-- Correctness: verification succeeds for honestly generated signatures -/
  correctness : ∀ (kp : KeyPair) (msg : ByteArray),
    verify (kp.1) msg (sign kp msg) = true

/-- Abstract hash function -/
class HashFunction (α : Type) where
  hash : α → Hash
  /-- Collision resistance (idealized property) -/
  collision_resistant : ∀ (x y : α), x ≠ y → hash x ≠ hash y

end IceNine.Crypto
