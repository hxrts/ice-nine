/-
# Cryptographic Primitives

Definitions and properties of cryptographic primitives used in the protocol.
-/

import Mathlib.Data.Fintype.Basic

namespace IceNine.Crypto

/-- A cryptographic key represented as a byte array -/
structure Key where
  bytes : ByteArray
  deriving DecidableEq

/-- A cryptographic signature -/
structure Signature where
  bytes : ByteArray
  deriving DecidableEq

/-- A hash digest -/
structure Hash where
  bytes : ByteArray
  deriving DecidableEq

/-- Abstract signature scheme -/
class SignatureScheme (KeyPair : Type) where
  /-- Extract the public key from a key pair -/
  publicKey : KeyPair → Key
  /-- Generate a key pair -/
  keygen : IO KeyPair
  /-- Sign a message -/
  sign : KeyPair → ByteArray → Signature
  /-- Verify a signature -/
  verify : Key → ByteArray → Signature → Bool
  /-- Correctness: verification succeeds for honestly generated signatures -/
  correctness : ∀ (kp : KeyPair) (msg : ByteArray),
    verify (publicKey kp) msg (sign kp msg) = true

/-- Abstract hash function -/
class HashFunction (α : Type) where
  hash : α → Hash
  /-- Collision resistance (idealized property) -/
  collision_resistant : ∀ (x y : α), x ≠ y → hash x ≠ hash y

end IceNine.Crypto
