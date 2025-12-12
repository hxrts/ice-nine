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

import IceNine.Protocol.Core.Core
import IceNine.Protocol.Sign.Types

namespace IceNine.Protocol.Serialize

/-!
## Serialization Header

Following FROST, all serialized messages include a header with:
- Protocol version: enables forward compatibility
- Scheme ID: identifies parameter set (e.g., ML-DSA-44, ML-DSA-65, ML-DSA-87)

This ensures messages can be validated before parsing and enables
safe protocol upgrades.
-/

/-- Protocol version for serialization format.
    Increment when making breaking changes to wire format. -/
def protocolVersion : UInt8 := 1

/-- Scheme identifiers for different parameter sets. -/
inductive SchemeId : Type
  | mlDsa44    -- ML-DSA-44 (128-bit security)
  | mlDsa65    -- ML-DSA-65 (192-bit security)
  | mlDsa87    -- ML-DSA-87 (256-bit security)
  | custom (id : ByteArray)  -- Custom/experimental schemes
  deriving DecidableEq

/-- Convert scheme ID to bytes. -/
def SchemeId.toBytes : SchemeId → ByteArray
  | .mlDsa44 => ⟨#[0x44]⟩
  | .mlDsa65 => ⟨#[0x65]⟩
  | .mlDsa87 => ⟨#[0x87]⟩
  | .custom id => ⟨#[0xFF]⟩ ++ id

/-- Parse scheme ID from bytes. -/
def SchemeId.fromByte : UInt8 → Option SchemeId
  | 0x44 => some .mlDsa44
  | 0x65 => some .mlDsa65
  | 0x87 => some .mlDsa87
  | _ => none

/-- Serialization header included in all protocol messages. -/
structure SerializationHeader where
  /-- Protocol version (for format compatibility) -/
  version : UInt8
  /-- Scheme/parameter set identifier -/
  schemeId : SchemeId
  deriving DecidableEq

/-- Default header for current protocol version. -/
def SerializationHeader.default (sid : SchemeId) : SerializationHeader :=
  { version := protocolVersion, schemeId := sid }

/-- Serialize header: version (1 byte) + schemeId (1+ bytes) -/
def SerializationHeader.toBytes (h : SerializationHeader) : ByteArray :=
  ⟨#[h.version]⟩ ++ h.schemeId.toBytes

/-- Parse header from bytes. Returns header and remaining bytes. -/
def SerializationHeader.fromBytes (bs : ByteArray) : Option (SerializationHeader × ByteArray) :=
  if bs.size < 2 then none
  else
    let version := bs.get! 0
    let schemeIdByte := bs.get! 1
    match SchemeId.fromByte schemeIdByte with
    | some sid =>
        if schemeIdByte = 0xFF then
          -- Custom scheme: read 4-byte length + data
          if bs.size < 6 then none
          else
            let b2 := bs.get! 2
            let b3 := bs.get! 3
            let len := b2.toNat + b3.toNat * 256
            if bs.size < 4 + len then none
            else
              let customId := bs.extract 4 (4 + len)
              some ({ version := version, schemeId := .custom customId },
                    bs.extract (4 + len) bs.size)
        else
          some ({ version := version, schemeId := sid }, bs.extract 2 bs.size)
    | none => none

/-- Validate header version compatibility. -/
def SerializationHeader.isCompatible (h : SerializationHeader) : Bool :=
  h.version ≤ protocolVersion

/-- Header validation error. -/
inductive HeaderError
  | versionMismatch (expected got : UInt8)
  | unknownScheme
  | malformedHeader
  deriving DecidableEq, Repr

/-- Validate and extract header from bytes. -/
def validateHeader (bs : ByteArray) (expectedScheme : Option SchemeId := none)
    : Except HeaderError (SerializationHeader × ByteArray) :=
  match SerializationHeader.fromBytes bs with
  | none => .error .malformedHeader
  | some (h, rest) =>
      if !h.isCompatible then
        .error (.versionMismatch protocolVersion h.version)
      else match expectedScheme with
        | none => .ok (h, rest)
        | some expected =>
            if h.schemeId = expected then .ok (h, rest)
            else .error .unknownScheme

/-!
## Parameter Set Registry

Standard parameter sets for ML-DSA (NIST FIPS 204).
Each set provides different security/performance tradeoffs.
-/

/-- Security level for a parameter set. -/
inductive SecurityLevel
  | bits128  -- NIST Level 1 (equivalent to AES-128)
  | bits192  -- NIST Level 3 (equivalent to AES-192)
  | bits256  -- NIST Level 5 (equivalent to AES-256)
  deriving DecidableEq, Repr

/-- Parameter set specification. -/
structure ParameterSet where
  /-- Scheme identifier for serialization -/
  schemeId : SchemeId
  /-- Security level -/
  securityLevel : SecurityLevel
  /-- Ring dimension (power of 2) -/
  n : Nat
  /-- Module rank -/
  k : Nat
  /-- Number of vectors in public key -/
  l : Nat
  /-- Modulus -/
  q : Nat
  /-- Challenge weight (number of ±1 entries) -/
  tau : Nat
  /-- Response norm bound (γ₁) -/
  gamma1 : Nat
  /-- Low bits rounding (γ₂) -/
  gamma2 : Nat
  /-- Rejection bound (β) -/
  beta : Nat
  deriving DecidableEq

/-- ML-DSA-44: 128-bit security (NIST Level 1) -/
def paramsMlDsa44 : ParameterSet :=
  { schemeId := .mlDsa44
    securityLevel := .bits128
    n := 256
    k := 4
    l := 4
    q := 8380417
    tau := 39
    gamma1 := 131072  -- 2^17
    gamma2 := 95232
    beta := 78
  }

/-- ML-DSA-65: 192-bit security (NIST Level 3) -/
def paramsMlDsa65 : ParameterSet :=
  { schemeId := .mlDsa65
    securityLevel := .bits192
    n := 256
    k := 6
    l := 5
    q := 8380417
    tau := 49
    gamma1 := 524288  -- 2^19
    gamma2 := 261888
    beta := 196
  }

/-- ML-DSA-87: 256-bit security (NIST Level 5) -/
def paramsMlDsa87 : ParameterSet :=
  { schemeId := .mlDsa87
    securityLevel := .bits256
    n := 256
    k := 8
    l := 7
    q := 8380417
    tau := 60
    gamma1 := 524288  -- 2^19
    gamma2 := 261888
    beta := 120
  }

/-- All standard parameter sets. -/
def standardParameterSets : List ParameterSet :=
  [paramsMlDsa44, paramsMlDsa65, paramsMlDsa87]

/-- Look up parameter set by scheme ID. -/
def ParameterSet.fromSchemeId : SchemeId → Option ParameterSet
  | .mlDsa44 => some paramsMlDsa44
  | .mlDsa65 => some paramsMlDsa65
  | .mlDsa87 => some paramsMlDsa87
  | .custom _ => none  -- Custom schemes need explicit parameters

/-- Look up parameter set by security level. -/
def ParameterSet.fromSecurityLevel : SecurityLevel → ParameterSet
  | .bits128 => paramsMlDsa44
  | .bits192 => paramsMlDsa65
  | .bits256 => paramsMlDsa87

/-- Check if parameters are within secure bounds.
    This is a basic sanity check, not a full security analysis. -/
def ParameterSet.isSecure (p : ParameterSet) : Bool :=
  p.n ≥ 256 &&
  p.k ≥ 4 &&
  p.q > p.beta * 2 &&
  p.gamma1 > p.beta

/-- Estimated public key size in bytes. -/
def ParameterSet.publicKeySize (p : ParameterSet) : Nat :=
  -- Compressed representation: seedA (32 bytes) + t1 (k * n * 10 bits)
  32 + (p.k * p.n * 10) / 8

/-- Estimated signature size in bytes. -/
def ParameterSet.signatureSize (p : ParameterSet) : Nat :=
  -- Challenge hash (32) + z (l * n * log γ₁ bits) + hints
  32 + (p.l * p.n * 18) / 8 + p.k

/-!
## Serializable Typeclass

The core abstraction for types that can be converted to/from bytes.
-/

/-- Typeclass for serializable types.
    Implementations must satisfy: fromBytes (toBytes x) = some x (round-trip). -/
class Serializable (α : Type*) where
  /-- Convert to byte representation -/
  toBytes : α → ByteArray
  /-- Parse from bytes, returning parsed value and bytes consumed. -/
  fromBytes : ByteArray → Option (α × Nat)
  -- Axiom: successful round-trip
  -- roundTrip : ∀ x, fromBytes (toBytes x) = some x

/-- Typeclass for types that serialize with a header. -/
class SerializableWithHeader (α : Type*) extends Serializable α where
  /-- The scheme ID for this type's serialization -/
  schemeId : SchemeId

/-- Serialize with header prefix -/
def SerializableWithHeader.toBytesWithHeader {α : Type*} [inst : SerializableWithHeader α] (x : α) : ByteArray :=
  (SerializationHeader.default inst.schemeId).toBytes ++ inst.toBytes x

/-- Parse with header validation -/
def SerializableWithHeader.fromBytesWithHeader {α : Type*} [inst : SerializableWithHeader α] (bs : ByteArray) : Option α :=
  match SerializationHeader.fromBytes bs with
  | none => none
  | some (h, rest) => if h.schemeId = inst.schemeId then (inst.fromBytes rest).map (·.1) else none

/-!
## ByteRead Effect

Algebraic effect signature for byte reading, with separate interpretation.
This separates the *description* of what to read from *how* to read it.

### Design

The `ByteRead` structure represents the current read state. Operations are
pure functions that take state and return `Except String (result × newState)`.
This gives us:
- Clear effect signature (the operations)
- Single interpretation (for efficiency)
- Easy testing (construct ByteRead directly)
- Composable via explicit state threading or `StateT` sugar
-/

/-- Read effect state: buffer and current position -/
structure ByteRead where
  buffer : ByteArray
  pos : Nat
  deriving BEq

/-- Result of a read operation: value and updated state -/
abbrev ReadResult (α : Type) := Except String (α × ByteRead)

namespace ByteRead

/-- Create initial read state from a ByteArray -/
def init (bs : ByteArray) : ByteRead := { buffer := bs, pos := 0 }

/-- Bytes remaining to read -/
def remaining (st : ByteRead) : Nat := st.buffer.size - st.pos

/-- Check if read is complete (all bytes consumed) -/
def isComplete (st : ByteRead) : Bool := st.pos = st.buffer.size

/-!
### Core Operations

Each operation takes state explicitly and returns updated state.
These are the "effect handlers" for our read effect.
-/

/-- Read exactly n bytes -/
def readBytes (n : Nat) (st : ByteRead) : ReadResult ByteArray :=
  if st.pos + n > st.buffer.size then
    .error s!"readBytes: need {n} bytes at position {st.pos}, buffer has {st.buffer.size}"
  else
    let result := st.buffer.extract st.pos (st.pos + n)
    .ok (result, { st with pos := st.pos + n })

/-- Read a single byte -/
def readByte (st : ByteRead) : ReadResult UInt8 :=
  if st.pos ≥ st.buffer.size then
    .error s!"readByte: end of buffer at position {st.pos}"
  else
    .ok (st.buffer.get! st.pos, { st with pos := st.pos + 1 })

/-- Peek at n bytes without advancing position -/
def peek (n : Nat) (st : ByteRead) : Except String ByteArray :=
  if st.pos + n > st.buffer.size then
    .error s!"peek: need {n} bytes at position {st.pos}"
  else
    .ok (st.buffer.extract st.pos (st.pos + n))

/-- Skip n bytes -/
def skip (n : Nat) (st : ByteRead) : ReadResult Unit :=
  if st.pos + n > st.buffer.size then
    .error s!"skip: need {n} bytes at position {st.pos}"
  else
    .ok ((), { st with pos := st.pos + n })

/-- Read 4-byte little-endian length prefix -/
def readLen32 (st : ByteRead) : ReadResult Nat :=
  match readBytes 4 st with
  | .error e => .error e
  | .ok (bs, st') =>
      let b0 := bs.get! 0 |>.toNat
      let b1 := bs.get! 1 |>.toNat
      let b2 := bs.get! 2 |>.toNat
      let b3 := bs.get! 3 |>.toNat
      .ok (b0 + b1 <<< 8 + b2 <<< 16 + b3 <<< 24, st')

/-- Read 8-byte little-endian Nat -/
def readNat64 (st : ByteRead) : ReadResult Nat :=
  match readBytes 8 st with
  | .error e => .error e
  | .ok (bs, st') =>
      let b0 := bs.get! 0 |>.toNat
      let b1 := bs.get! 1 |>.toNat
      let b2 := bs.get! 2 |>.toNat
      let b3 := bs.get! 3 |>.toNat
      let b4 := bs.get! 4 |>.toNat
      let b5 := bs.get! 5 |>.toNat
      let b6 := bs.get! 6 |>.toNat
      let b7 := bs.get! 7 |>.toNat
      .ok (b0 + b1 <<< 8 + b2 <<< 16 + b3 <<< 24 +
           b4 <<< 32 + b5 <<< 40 + b6 <<< 48 + b7 <<< 56, st')

end ByteRead

/-!
### Composition via StateT

For convenience, we provide `ByteReader` as `StateT ByteRead (Except String)`.
This allows monadic composition with `do` notation while using the same
underlying effect operations.
-/

/-- ByteReader: StateT wrapper for monadic composition -/
abbrev ByteReader := StateT ByteRead (Except String)

namespace ByteReader

/-- Run a reader on a ByteArray, returning value and bytes consumed -/
def run {α : Type} (r : ByteReader α) (bs : ByteArray) : Option (α × Nat) :=
  match StateT.run r (ByteRead.init bs) with
  | .ok (a, st) => some (a, st.pos)
  | .error _ => none

/-- Run with error reporting -/
def runWithError {α : Type} (r : ByteReader α) (bs : ByteArray) : Except String (α × Nat) :=
  match StateT.run r (ByteRead.init bs) with
  | .ok (a, st) => .ok (a, st.pos)
  | .error e => .error e

/-- Lift ByteRead operation into ByteReader -/
def lift {α : Type} (op : ByteRead → ReadResult α) : ByteReader α := do
  let st ← get
  match op st with
  | .ok (a, st') => set st'; return a
  | .error e => throw e

/-- Read exactly n bytes -/
def readBytes (n : Nat) : ByteReader ByteArray := lift (ByteRead.readBytes n)

/-- Read a single byte -/
def readByte : ByteReader UInt8 := lift ByteRead.readByte

/-- Peek at n bytes without advancing -/
def peek (n : Nat) : ByteReader ByteArray := do
  let st ← get
  match ByteRead.peek n st with
  | .ok bs => return bs
  | .error e => throw e

/-- Get remaining byte count -/
def remaining : ByteReader Nat := do
  let st ← get
  return st.remaining

/-- Skip n bytes -/
def skip (n : Nat) : ByteReader Unit := lift (ByteRead.skip n)

/-- Read 4-byte length prefix -/
def readLen32 : ByteReader Nat := lift ByteRead.readLen32

/-- Read 8-byte Nat -/
def readNat64 : ByteReader Nat := lift ByteRead.readNat64

/-- Read a value using its Serializable instance -/
def read {α : Type} [Serializable α] : ByteReader α := do
  let st ← get
  let rest := st.buffer.extract st.pos st.buffer.size
  match Serializable.fromBytes rest with
  | some (a, consumed) =>
      set { st with pos := st.pos + consumed }
      return a
  | none => throw s!"read: failed to deserialize at position {st.pos}"

end ByteReader

/-!
## Primitive Serializers

Basic serialization for Nat, Int, and ByteArray.
Uses ByteReader for safe deserialization.
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

/-- Decode Nat from 8-byte little-endian using ByteReader -/
def natFromBytesReader : ByteReader Nat := do
  let bs ← ByteReader.readBytes 8
  let b0 := bs.get! 0 |>.toNat
  let b1 := bs.get! 1 |>.toNat
  let b2 := bs.get! 2 |>.toNat
  let b3 := bs.get! 3 |>.toNat
  let b4 := bs.get! 4 |>.toNat
  let b5 := bs.get! 5 |>.toNat
  let b6 := bs.get! 6 |>.toNat
  let b7 := bs.get! 7 |>.toNat
  return b0 + b1 <<< 8 + b2 <<< 16 + b3 <<< 24 +
         b4 <<< 32 + b5 <<< 40 + b6 <<< 48 + b7 <<< 56

/-- Encode Int as 8-byte little-endian (two's complement) -/
def intToBytes (i : Int) : ByteArray :=
  let n := if i < 0 then (2^64 : Nat) - i.natAbs else i.toNat
  natToBytes n

/-- Decode Int from 8-byte little-endian using ByteReader -/
def intFromBytesReader : ByteReader Int := do
  let n ← natFromBytesReader
  return if n ≥ 2^63 then Int.negOfNat (2^64 - n) else Int.ofNat n

instance : Serializable Nat where
  toBytes := natToBytes
  fromBytes bs := natFromBytesReader.run bs

instance : Serializable Int where
  toBytes := intToBytes
  fromBytes bs := intFromBytesReader.run bs

/-- Write 4-byte length prefix -/
def writeLen32 (n : Nat) : ByteArray :=
  natToBytes n |>.extract 0 4

/-- ByteReader for ByteArray: 4-byte length + data -/
def byteArrayReader : ByteReader ByteArray := do
  let len ← ByteReader.readLen32
  ByteReader.readBytes len

instance : Serializable ByteArray where
  toBytes bs := writeLen32 bs.size ++ bs
  fromBytes bs := byteArrayReader.run bs

/-!
## Compound Type Serializers

Serialization for Option, List, and product types.
Uses ByteReader for safe, composable deserialization.
-/

/-- ByteReader for Option: 0x00 for none, 0x01 + value for some -/
def optionReader {α : Type} [Serializable α] : ByteReader (Option α) := do
  let tag ← ByteReader.readByte
  match tag with
  | 0 => return none
  | 1 => return some (← (ByteReader.read : ByteReader α))
  | t => throw s!"optionReader: invalid tag {t}, expected 0 or 1"

instance {α : Type} [Serializable α] : Serializable (Option α) where
  toBytes
    | none => ⟨#[0]⟩
    | some x => ⟨#[1]⟩ ++ Serializable.toBytes x
  fromBytes bs := optionReader.run bs

/-- ByteReader for List: 4-byte count + elements -/
def listReader {α : Type} [Serializable α] : ByteReader (List α) := do
  let count ← ByteReader.readLen32
  let mut acc : List α := []
  for _ in [:count] do
    let x ← (ByteReader.read : ByteReader α)
    acc := x :: acc
  return acc.reverse

instance {α : Type} [Serializable α] : Serializable (List α) where
  toBytes xs :=
    let count := writeLen32 xs.length
    let elements := xs.foldl (fun acc x => acc ++ Serializable.toBytes x) ByteArray.empty
    count ++ elements
  fromBytes bs := listReader.run bs

/-!
## Protocol Message Serializers

Bidirectional serialization for DKG and signing messages.
Each message type has paired encode/decode functions using ByteReader.
-/

-- ProofOfKnowledge: commitment (R) + response (μ)
section ProofOfKnowledge
variable (S : Scheme) [Serializable S.Public] [Serializable S.Secret]

def serializeProofOfKnowledge (pok : ProofOfKnowledge S) : ByteArray :=
  Serializable.toBytes pok.commitment ++ Serializable.toBytes pok.response

def deserializeProofOfKnowledge : ByteReader (ProofOfKnowledge S) := do
  let commitment ← (ByteReader.read : ByteReader S.Public)
  let response ← (ByteReader.read : ByteReader S.Secret)
  return { commitment, response }

instance : Serializable (ProofOfKnowledge S) where
  toBytes := serializeProofOfKnowledge S
  fromBytes bs := (deserializeProofOfKnowledge S).run bs
end ProofOfKnowledge

-- DkgCommitMsg: sender + commitment + proof of knowledge
section DkgCommitMsg
variable (S : Scheme) [Serializable S.PartyId] [Serializable S.Commitment]
         [Serializable S.Public] [Serializable S.Secret]

def serializeDkgCommitMsg (msg : DkgCommitMsg S) : ByteArray :=
  Serializable.toBytes msg.sender ++
  Serializable.toBytes msg.commitPk ++
  serializeProofOfKnowledge S msg.pok

def deserializeDkgCommitMsg : ByteReader (DkgCommitMsg S) := do
  let sender ← (ByteReader.read : ByteReader S.PartyId)
  let commitPk ← (ByteReader.read : ByteReader S.Commitment)
  let pok ← deserializeProofOfKnowledge S
  return { sender, commitPk, pok }

instance : Serializable (DkgCommitMsg S) where
  toBytes := serializeDkgCommitMsg S
  fromBytes bs := (deserializeDkgCommitMsg S).run bs
end DkgCommitMsg

-- DkgRevealMsg: sender + pk_i + opening
section DkgRevealMsg
variable (S : Scheme) [Serializable S.PartyId] [Serializable S.Public] [Serializable S.Opening]

def serializeDkgRevealMsg (msg : DkgRevealMsg S) : ByteArray :=
  Serializable.toBytes msg.sender ++
  Serializable.toBytes msg.pk_i ++
  Serializable.toBytes msg.opening

def deserializeDkgRevealMsg : ByteReader (DkgRevealMsg S) := do
  let sender ← (ByteReader.read : ByteReader S.PartyId)
  let pk_i ← (ByteReader.read : ByteReader S.Public)
  let opening ← (ByteReader.read : ByteReader S.Opening)
  return { sender, pk_i, opening }

instance : Serializable (DkgRevealMsg S) where
  toBytes := serializeDkgRevealMsg S
  fromBytes bs := (deserializeDkgRevealMsg S).run bs
end DkgRevealMsg

-- SignCommitMsg: sender + session + commitW + hiding + binding
section SignCommitMsg
variable (S : Scheme) [Serializable S.PartyId] [Serializable S.Commitment] [Serializable S.Public]

def serializeSignCommitMsg (msg : SignCommitMsg S) : ByteArray :=
  Serializable.toBytes msg.sender ++
  Serializable.toBytes msg.session ++
  Serializable.toBytes msg.commitW ++
  Serializable.toBytes msg.hidingVal ++
  Serializable.toBytes msg.bindingVal

def deserializeSignCommitMsg : ByteReader (SignCommitMsg S) := do
  let sender ← (ByteReader.read : ByteReader S.PartyId)
  let session ← (ByteReader.read : ByteReader Nat)
  let commitW ← (ByteReader.read : ByteReader S.Commitment)
  let hidingVal ← (ByteReader.read : ByteReader S.Public)
  let bindingVal ← (ByteReader.read : ByteReader S.Public)
  return { sender, session, commitW, hidingVal, bindingVal }

instance : Serializable (SignCommitMsg S) where
  toBytes := serializeSignCommitMsg S
  fromBytes bs := (deserializeSignCommitMsg S).run bs
end SignCommitMsg

-- SignRevealWMsg: sender + session + opening
section SignRevealWMsg
variable (S : Scheme) [Serializable S.PartyId] [Serializable S.Opening]

def serializeSignRevealWMsg (msg : SignRevealWMsg S) : ByteArray :=
  Serializable.toBytes msg.sender ++
  Serializable.toBytes msg.session ++
  Serializable.toBytes msg.opening

def deserializeSignRevealWMsg : ByteReader (SignRevealWMsg S) := do
  let sender ← (ByteReader.read : ByteReader S.PartyId)
  let session ← (ByteReader.read : ByteReader Nat)
  let opening ← (ByteReader.read : ByteReader S.Opening)
  return { sender, session, opening }

instance : Serializable (SignRevealWMsg S) where
  toBytes := serializeSignRevealWMsg S
  fromBytes bs := (deserializeSignRevealWMsg S).run bs
end SignRevealWMsg

-- SignShareMsg: sender + session + z_i
section SignShareMsg
variable (S : Scheme) [Serializable S.PartyId] [Serializable S.Secret]

def serializeSignShareMsg (msg : SignShareMsg S) : ByteArray :=
  Serializable.toBytes msg.sender ++
  Serializable.toBytes msg.session ++
  Serializable.toBytes msg.z_i

def deserializeSignShareMsg : ByteReader (SignShareMsg S) := do
  let sender ← (ByteReader.read : ByteReader S.PartyId)
  let session ← (ByteReader.read : ByteReader Nat)
  let z_i ← (ByteReader.read : ByteReader S.Secret)
  return { sender, session, z_i }

instance : Serializable (SignShareMsg S) where
  toBytes := serializeSignShareMsg S
  fromBytes bs := (deserializeSignShareMsg S).run bs
end SignShareMsg

-- Signature: z + c + Sset + commits
section Signature
variable (S : Scheme) [Serializable S.Secret] [Serializable S.Challenge]
                      [Serializable S.PartyId] [Serializable S.Commitment]

def serializeSignature (sig : Signature S) : ByteArray :=
  Serializable.toBytes sig.z ++
  Serializable.toBytes sig.c ++
  Serializable.toBytes sig.Sset ++
  Serializable.toBytes sig.commits

def deserializeSignature : ByteReader (Signature S) := do
  let z ← (ByteReader.read : ByteReader S.Secret)
  let c ← (ByteReader.read : ByteReader S.Challenge)
  let Sset ← (ByteReader.read : ByteReader (List S.PartyId))
  let commits ← (ByteReader.read : ByteReader (List S.Commitment))
  return { z, c, Sset, commits }

instance : Serializable (Signature S) where
  toBytes := serializeSignature S
  fromBytes bs := (deserializeSignature S).run bs
end Signature

/-!
## Message Wrapper for Network Transport

Wraps any message with a type tag and length for network transport.
-/

/-- Message type tags for protocol messages.

    Note: `abort` tag has been removed. With local rejection sampling,
    there is no distributed abort coordination—signing either succeeds
    locally or fails without network communication. -/
inductive MessageTag : Type
  | dkgCommit | dkgReveal
  | signCommit | signReveal | signShare
  | signature
  deriving DecidableEq, Repr

/-- Convert tag to byte -/
def MessageTag.toByte : MessageTag → UInt8
  | .dkgCommit => 0x01
  | .dkgReveal => 0x02
  | .signCommit => 0x10
  | .signReveal => 0x11
  | .signShare => 0x12
  | .signature => 0x20

/-- Parse tag from byte -/
def MessageTag.fromByte : UInt8 → Option MessageTag
  | 0x01 => some .dkgCommit
  | 0x02 => some .dkgReveal
  | 0x10 => some .signCommit
  | 0x11 => some .signReveal
  | 0x12 => some .signShare
  | 0x20 => some .signature
  | _ => none

/-- Wrapped message with tag and length for network transport -/
structure WrappedMessage where
  tag : MessageTag
  payload : ByteArray
deriving DecidableEq

/-- Serialize wrapped message: tag (1 byte) + length (4 bytes) + payload -/
def WrappedMessage.toBytes (msg : WrappedMessage) : ByteArray :=
  ⟨#[msg.tag.toByte]⟩ ++ writeLen32 msg.payload.size ++ msg.payload

/-- ByteReader for wrapped message -/
def wrappedMessageReader : ByteReader WrappedMessage := do
  let tagByte ← ByteReader.readByte
  match MessageTag.fromByte tagByte with
  | some tag =>
      let len ← ByteReader.readLen32
      let payload ← ByteReader.readBytes len
      return { tag, payload }
  | none => throw s!"wrappedMessageReader: unknown tag {tagByte}"

/-- Parse wrapped message -/
def WrappedMessage.fromBytes (bs : ByteArray) : Option WrappedMessage :=
  (wrappedMessageReader.run bs).map (·.1)

instance : Serializable WrappedMessage where
  toBytes := WrappedMessage.toBytes
  fromBytes bs := wrappedMessageReader.run bs

/-!
## Convenience Functions

High-level serialization functions for common operations.
-/

/-- Wrap a DKG commit message for transport -/
def wrapDkgCommit (S : Scheme)
    [Serializable S.PartyId] [Serializable S.Commitment]
    [Serializable S.Public] [Serializable S.Secret]
    (msg : DkgCommitMsg S) : WrappedMessage :=
  { tag := .dkgCommit, payload := serializeDkgCommitMsg S msg }

/-- Wrap a sign commit message for transport (dual nonce) -/
def wrapSignCommit (S : Scheme)
    [Serializable S.PartyId] [Serializable S.Commitment] [Serializable S.Public]
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
    -- Use ByteReader to parse 4-byte length (padded to 8 bytes for natFromBytesReader)
    match natFromBytesReader.run (lenBytes ++ ⟨#[0, 0, 0, 0]⟩) with
    | some (len, _) => bs.size ≥ 5 + len
    | none => false

/-- Get message tag without full parsing -/
def peekMessageTag (bs : ByteArray) : Option MessageTag :=
  if bs.size < 1 then none
  else MessageTag.fromByte (bs.get! 0)

/-!
## Round-Trip Testing

Infrastructure for verifying serialization round-trips correctly.
Use these in tests to catch encode/decode mismatches.
-/

/-- Check that a value round-trips through serialization.
    Returns `true` if `fromBytes (toBytes x) = some (x, _)` -/
def checkRoundTrip {α : Type} [Serializable α] [BEq α] (x : α) : Bool :=
  match Serializable.fromBytes (Serializable.toBytes x) with
  | some (y, _) => x == y
  | none => false

/-- Check round-trip with detailed error reporting -/
def checkRoundTripWithError {α : Type} [Serializable α] [BEq α] [Repr α]
    (x : α) : Except String Unit :=
  let bytes := Serializable.toBytes x
  match Serializable.fromBytes bytes with
  | some (y, consumed) =>
      if x == y then
        if consumed = bytes.size then .ok ()
        else .error s!"round-trip ok but consumed {consumed} of {bytes.size} bytes"
      else .error s!"round-trip mismatch: input {repr x}, output {repr y}"
  | none => .error s!"deserialization failed for {repr x} (bytes: {bytes.size})"

/-- Check round-trip using ByteReader with error details -/
def checkRoundTripReader {α : Type} [Serializable α] [BEq α] [Repr α]
    (x : α) : Except String Unit :=
  let bytes := Serializable.toBytes x
  match ByteReader.runWithError (ByteReader.read : ByteReader α) bytes with
  | .ok (y, consumed) =>
      if x == y then
        if consumed = bytes.size then .ok ()
        else .error s!"round-trip ok but consumed {consumed} of {bytes.size} bytes"
      else .error s!"round-trip mismatch: input {repr x}, output {repr y}"
  | .error e => .error s!"deserialization failed: {e}"

/-- Property: serialization is injective (different values → different bytes) -/
def checkInjective {α : Type} [Serializable α] [BEq α] (x y : α) : Bool :=
  if x == y then true
  else Serializable.toBytes x != Serializable.toBytes y

/-- Property: deserialization consumes all bytes for exact-length input -/
def checkExactConsumption {α : Type} [Serializable α] (x : α) : Bool :=
  let bytes := Serializable.toBytes x
  match Serializable.fromBytes (α := α) bytes with
  | some (_, consumed) => consumed = bytes.size
  | none => false

end IceNine.Protocol.Serialize
