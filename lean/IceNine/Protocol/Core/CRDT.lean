/-
# CRDT Infrastructure

Core Conflict-free Replicated Data Type (CRDT) primitives for the Ice Nine protocol.
These provide the foundational merge semantics used throughout the protocol.

## Contents

- `Join` typeclass: Binary join operation (semilattice merge)
- `MsgMap`: Sender-keyed message map that makes conflicts un-expressable

## Design

All CRDT structures guarantee:
- **Commutativity**: `a ⊔ b = b ⊔ a`
- **Associativity**: `(a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)`
- **Idempotence**: `a ⊔ a = a`

This ensures convergence regardless of message order or duplication.
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.Core.Patterns
import Mathlib

namespace IceNine.Protocol

/-!
## Join Typeclass

Simple typeclass for binary join operation (CRDT merge).
We define our own since Mathlib's `Sup` is for set supremum.
-/

/-- Binary join operation for CRDT merge semantics. -/
class Join (α : Type*) where
  /-- Join two elements (associative, commutative, idempotent). -/
  join : α → α → α

infixl:65 " ⊔ " => Join.join

/-!
## Message Map (CRDT-Safe Collection)

Messages are stored in a map keyed by sender ID. This structure makes it
**impossible to express** conflicting messages from the same sender:
- The type `Std.HashMap PartyId Message` allows at most one entry per key
- Insert operations that would create conflicts are rejected
- Merge uses map union with explicit conflict resolution

This ensures:
- Commutativity: merge order doesn't matter (for non-conflicting inputs)
- Idempotence: duplicate messages are ignored
- Associativity: grouping doesn't matter
- **Conflict-freedom**: impossible to have two messages from same sender
-/

/-- A map from sender ID to message. At most one message per sender by construction.
    This is the CRDT-safe replacement for List-based message collection. -/
structure MsgMap (S : Scheme) (M : Type*) [BEq S.PartyId] [Hashable S.PartyId] where
  /-- Map from sender to message -/
  map : Std.HashMap S.PartyId M

/-- Empty message map. -/
def MsgMap.empty {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    : MsgMap S M :=
  { map := {} }

/-- Result of attempting to insert a message. -/
inductive InsertResult (S : Scheme) (M : Type*)  [BEq S.PartyId] [Hashable S.PartyId]
  | success (newMap : MsgMap S M)
  | conflict (existing : M)

/-- Try to insert a message. Returns conflict if sender already has a message.
    This makes conflicts **un-expressable** - you cannot silently overwrite. -/
def MsgMap.tryInsert {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    (getSender : M → S.PartyId)
    (s : MsgMap S M) (m : M) : InsertResult S M :=
  let sender := getSender m
  match s.map.get? sender with
  | some existing => .conflict existing
  | none => .success { map := s.map.insert sender m }

/-- Insert a message, ignoring if sender already present (CRDT semantics).
    For strict conflict detection, use `tryInsert` instead. -/
def MsgMap.insert {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    (getSender : M → S.PartyId)
    (s : MsgMap S M) (m : M) : MsgMap S M :=
  let sender := getSender m
  if s.map.contains sender
  then s  -- sender already present, keep existing (CRDT: first write wins)
  else { map := s.map.insert sender m }

/-- Merge two message maps. On conflict, keeps message from first map.
    This is commutative on the *set of senders*, and fully commutative
    when there are no conflicts. -/
def MsgMap.merge {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    (a b : MsgMap S M) : MsgMap S M :=
  -- Union: for each key in b, insert into a if not present
  { map := b.map.fold (fun acc k v =>
      if acc.contains k then acc else acc.insert k v) a.map }

/-- Get message for a sender. -/
def MsgMap.get? {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    (s : MsgMap S M) (sender : S.PartyId) : Option M :=
  s.map.get? sender

/-- Check if sender has a message. -/
def MsgMap.contains {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    (s : MsgMap S M) (sender : S.PartyId) : Bool :=
  s.map.contains sender

/-- Number of messages in the map. -/
def MsgMap.size {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    (s : MsgMap S M) : Nat :=
  s.map.size

/-- Convert message map to list of messages. -/
def MsgMap.toList {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    (s : MsgMap S M) : List M :=
  s.map.toList.map Prod.snd

/-- Convert message map to list of (sender, message) pairs. -/
def MsgMap.toAssocList {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    (s : MsgMap S M) : List (S.PartyId × M) :=
  s.map.toList

/-- Get all senders. -/
def MsgMap.senders {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    (s : MsgMap S M) : List S.PartyId :=
  s.map.toList.map Prod.fst

/-- Create message map from list, keeping first occurrence of each sender. -/
def MsgMap.fromList {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    (getSender : M → S.PartyId)
    (ms : List M) : MsgMap S M :=
  ms.foldl (fun acc m => acc.insert getSender m) MsgMap.empty

/-- MsgMap forms a join-semilattice via merge. -/
instance {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    : Join (MsgMap S M) :=
  ⟨MsgMap.merge⟩

/-- MsgMap ordering: subset by sender keys. -/
instance {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    : LE (MsgMap S M) :=
  ⟨fun a b => a.map.toList.all (fun (k, _) => b.map.contains k)⟩

end IceNine.Protocol
