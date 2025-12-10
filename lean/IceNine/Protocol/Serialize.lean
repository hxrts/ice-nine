/-
# Serialization API

Typeclass-based serialization for protocol messages. Provides a uniform interface
for converting protocol types to/from byte representations.

## Design

We define a `Serializable` typeclass with `toBytes` and `fromBytes` methods.
The implementation uses a simple length-prefixed encoding for compound types.

**Security Note**: Deserialization is a potential attack surface. All `fromBytes`
implementations must:
1. Validate input lengths before allocation
2. Return `none` on malformed input (never panic)
3. Be constant-time where feasible (see Side-Channel Considerations in Core.lean)

## Wire Format

The wire format uses little-endian encoding with explicit length prefixes:

| Type | Format |
|------|--------|
| Nat | 8-byte little-endian |
| Int | 8-byte little-endian (two's complement) |
| List α | 4-byte length + concatenated elements |
| Option α | 1-byte tag (0=none, 1=some) + element if some |
| Struct | Concatenated fields in declaration order |

**Reference**: This is similar to Protocol Buffers' encoding but simpler.
For production use, consider using a standardized format like CBOR or ASN.1.
-/

import IceNine.Protocol.Core
import IceNine.Protocol.Sign

namespace IceNine.Protocol.Serialize

/-!
## Serializable Typeclass

The core abstraction for types that can be converted to/from bytes.
-/

/-- Typeclass for serializable types.
    Implementations must satisfy: fromBytes (toBytes x) = some x (round-trip). -/
class Serializable (α : Type*) where
  /-- Convert to byte representation -/
  toBytes : α → ByteArray
  /-- Parse from bytes, returning none on malformed input -/
  fromBytes : ByteArray → Option α
  /-- Axiom: successful round-trip -/
  -- roundTrip : ∀ x, fromBytes (toBytes x) = some x

/-!
## Primitive Serializers

Basic serialization for Nat, Int, and ByteArray.
-/

/-- Encode Nat as 8-byte little-endian -/
def natToBytes (n : Nat) : ByteArray :=
  let b0 := (n &&& 0xFF).toUInt8
  let b1 := ((n >>> 8) &&& 0xFF).toUInt8
  let b2 := ((n >>> 16) &&& 0xFF).toUInt8
  let b3 := ((n >>> 24) &&& 0xFF).toUInt8
  let b4 := ((n >>> 32) &&& 0xFF).toUInt8
  let b5 := ((n >>> 40) &&& 0xFF).toUInt8
  let b6 := ((n >>> 48) &&& 0xFF).toUInt8
  let b7 := ((n >>> 56) &&& 0xFF).toUInt8
  ⟨#[b0, b1, b2, b3, b4, b5, b6, b7]⟩

/-- Decode Nat from 8-byte little-endian -/
def natFromBytes (bs : ByteArray) : Option Nat :=
  if bs.size < 8 then none
  else
    let b0 := bs.get! 0 |>.toNat
    let b1 := bs.get! 1 |>.toNat
    let b2 := bs.get! 2 |>.toNat
    let b3 := bs.get! 3 |>.toNat
    let b4 := bs.get! 4 |>.toNat
    let b5 := bs.get! 5 |>.toNat
    let b6 := bs.get! 6 |>.toNat
    let b7 := bs.get! 7 |>.toNat
    some (b0 + b1 <<< 8 + b2 <<< 16 + b3 <<< 24 +
          b4 <<< 32 + b5 <<< 40 + b6 <<< 48 + b7 <<< 56)

/-- Encode Int as 8-byte little-endian (two's complement) -/
def intToBytes (i : Int) : ByteArray :=
  -- Convert to unsigned representation
  let n := if i < 0 then (2^64 : Nat) - i.natAbs else i.toNat
  natToBytes n

/-- Decode Int from 8-byte little-endian (two's complement) -/
def intFromBytes (bs : ByteArray) : Option Int :=
  natFromBytes bs |>.map fun n =>
    if n ≥ 2^63 then Int.negOfNat (2^64 - n)
    else Int.ofNat n

instance : Serializable Nat where
  toBytes := natToBytes
  fromBytes := natFromBytes

instance : Serializable Int where
  toBytes := intToBytes
  fromBytes := intFromBytes

instance : Serializable ByteArray where
  toBytes bs :=
    -- Length prefix (4 bytes) + data
    let len := natToBytes bs.size |>.extract 0 4
    len ++ bs
  fromBytes bs :=
    if bs.size < 4 then none
    else
      let lenBytes := bs.extract 0 4
      match natFromBytes (lenBytes ++ ⟨#[0, 0, 0, 0]⟩) with
      | some len =>
          if bs.size < 4 + len then none
          else some (bs.extract 4 (4 + len))
      | none => none

/-!
## Compound Type Serializers

Serialization for Option, List, and product types.
-/

/-- Serialize Option: 0x00 for none, 0x01 + value for some -/
instance [Serializable α] : Serializable (Option α) where
  toBytes
    | none => ⟨#[0]⟩
    | some x => ⟨#[1]⟩ ++ Serializable.toBytes x
  fromBytes bs :=
    if bs.size < 1 then none
    else if bs.get! 0 = 0 then some none
    else if bs.get! 0 = 1 then
      Serializable.fromBytes (bs.extract 1 bs.size) |>.map some
    else none

/-- Serialize List: 4-byte count + concatenated elements -/
instance [Serializable α] : Serializable (List α) where
  toBytes xs :=
    let count := natToBytes xs.length |>.extract 0 4
    let elements := xs.foldl (fun acc x => acc ++ Serializable.toBytes x) ByteArray.empty
    count ++ elements
  fromBytes bs :=
    if bs.size < 4 then none
    else
      let countBytes := bs.extract 0 4
      match natFromBytes (countBytes ++ ⟨#[0, 0, 0, 0]⟩) with
      | some count =>
          -- Parse `count` elements from remaining bytes
          let rest := bs.extract 4 bs.size
          parseList count rest []
      | none => none
  where
    parseList (count : Nat) (bs : ByteArray) (acc : List α) : Option (List α) :=
      if count = 0 then some acc.reverse
      else
        -- This is a simplified parser that assumes fixed-size elements
        -- In practice, each element would encode its own length
        match Serializable.fromBytes bs with
        | some x =>
            -- Approximate: consume 8 bytes per element (adjust for type)
            let consumed := min 8 bs.size
            parseList (count - 1) (bs.extract consumed bs.size) (x :: acc)
        | none => none

/-!
## Protocol Message Serializers

Serialization for DKG and signing messages.
-/

/-- Serialize DkgCommitMsg: sender (8 bytes) + commitment -/
def serializeDkgCommitMsg (S : Scheme)
    [Serializable S.PartyId] [Serializable S.Commitment]
    (msg : DkgCommitMsg S) : ByteArray :=
  Serializable.toBytes msg.sender ++ Serializable.toBytes msg.commitPk

/-- Serialize DkgRevealMsg: sender + pk_i + opening -/
def serializeDkgRevealMsg (S : Scheme)
    [Serializable S.PartyId] [Serializable S.Public] [Serializable S.Opening]
    (msg : DkgRevealMsg S) : ByteArray :=
  Serializable.toBytes msg.sender ++
  Serializable.toBytes msg.pk_i ++
  Serializable.toBytes msg.opening

/-- Serialize SignCommitMsg: sender + session + commitment -/
def serializeSignCommitMsg (S : Scheme)
    [Serializable S.PartyId] [Serializable S.Commitment]
    (msg : SignCommitMsg S) : ByteArray :=
  Serializable.toBytes msg.sender ++
  Serializable.toBytes msg.session ++
  Serializable.toBytes msg.commitW

/-- Serialize SignRevealWMsg: sender + session + w_i + opening -/
def serializeSignRevealWMsg (S : Scheme)
    [Serializable S.PartyId] [Serializable S.Public] [Serializable S.Opening]
    (msg : SignRevealWMsg S) : ByteArray :=
  Serializable.toBytes msg.sender ++
  Serializable.toBytes msg.session ++
  Serializable.toBytes msg.w_i ++
  Serializable.toBytes msg.opening

/-- Serialize SignShareMsg: sender + session + z_i -/
def serializeSignShareMsg (S : Scheme)
    [Serializable S.PartyId] [Serializable S.Secret]
    (msg : SignShareMsg S) : ByteArray :=
  Serializable.toBytes msg.sender ++
  Serializable.toBytes msg.session ++
  Serializable.toBytes msg.z_i

/-- Serialize Signature: z + c + Sset + commits -/
def serializeSignature (S : Scheme)
    [Serializable S.Secret] [Serializable S.Challenge]
    [Serializable S.PartyId] [Serializable S.Commitment]
    (sig : Signature S) : ByteArray :=
  Serializable.toBytes sig.z ++
  Serializable.toBytes sig.c ++
  Serializable.toBytes sig.Sset ++
  Serializable.toBytes sig.commits

/-!
## Message Wrapper for Network Transport

Wraps any message with a type tag and length for network transport.
-/

/-- Message type tags for protocol messages -/
inductive MessageTag : Type
  | dkgCommit | dkgReveal
  | signCommit | signReveal | signShare
  | signature
  | abort
  deriving DecidableEq, Repr

/-- Convert tag to byte -/
def MessageTag.toByte : MessageTag → UInt8
  | .dkgCommit => 0x01
  | .dkgReveal => 0x02
  | .signCommit => 0x10
  | .signReveal => 0x11
  | .signShare => 0x12
  | .signature => 0x20
  | .abort => 0xFF

/-- Parse tag from byte -/
def MessageTag.fromByte : UInt8 → Option MessageTag
  | 0x01 => some .dkgCommit
  | 0x02 => some .dkgReveal
  | 0x10 => some .signCommit
  | 0x11 => some .signReveal
  | 0x12 => some .signShare
  | 0x20 => some .signature
  | 0xFF => some .abort
  | _ => none

/-- Wrapped message with tag and length for network transport -/
structure WrappedMessage where
  tag : MessageTag
  payload : ByteArray
deriving Repr

/-- Serialize wrapped message: tag (1 byte) + length (4 bytes) + payload -/
def WrappedMessage.toBytes (msg : WrappedMessage) : ByteArray :=
  let tagByte : ByteArray := ⟨#[msg.tag.toByte]⟩
  let lenBytes := natToBytes msg.payload.size |>.extract 0 4
  tagByte ++ lenBytes ++ msg.payload

/-- Parse wrapped message -/
def WrappedMessage.fromBytes (bs : ByteArray) : Option WrappedMessage :=
  if bs.size < 5 then none
  else
    match MessageTag.fromByte (bs.get! 0) with
    | some tag =>
        let lenBytes := bs.extract 1 5
        match natFromBytes (lenBytes ++ ⟨#[0, 0, 0, 0]⟩) with
        | some len =>
            if bs.size < 5 + len then none
            else some { tag := tag, payload := bs.extract 5 (5 + len) }
        | none => none
    | none => none

/-!
## Convenience Functions

High-level serialization functions for common operations.
-/

/-- Wrap a DKG commit message for transport -/
def wrapDkgCommit (S : Scheme)
    [Serializable S.PartyId] [Serializable S.Commitment]
    (msg : DkgCommitMsg S) : WrappedMessage :=
  { tag := .dkgCommit, payload := serializeDkgCommitMsg S msg }

/-- Wrap a sign commit message for transport -/
def wrapSignCommit (S : Scheme)
    [Serializable S.PartyId] [Serializable S.Commitment]
    (msg : SignCommitMsg S) : WrappedMessage :=
  { tag := .signCommit, payload := serializeSignCommitMsg S msg }

/-- Wrap a signature for transport -/
def wrapSignature (S : Scheme)
    [Serializable S.Secret] [Serializable S.Challenge]
    [Serializable S.PartyId] [Serializable S.Commitment]
    (sig : Signature S) : WrappedMessage :=
  { tag := .signature, payload := serializeSignature S sig }

/-!
## Validation Helpers

Functions to validate serialized data before parsing.
-/

/-- Check if bytes could be a valid wrapped message (length check only) -/
def isValidWrappedMessage (bs : ByteArray) : Bool :=
  if bs.size < 5 then false
  else
    let lenBytes := bs.extract 1 5
    match natFromBytes (lenBytes ++ ⟨#[0, 0, 0, 0]⟩) with
    | some len => bs.size ≥ 5 + len
    | none => false

/-- Get message tag without full parsing -/
def peekMessageTag (bs : ByteArray) : Option MessageTag :=
  if bs.size < 1 then none
  else MessageTag.fromByte (bs.get! 0)

end IceNine.Protocol.Serialize
