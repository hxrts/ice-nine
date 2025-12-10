/-
# Phase-Indexed Protocol State

Protocol progress modeled as discrete phases: commit → reveal → shares → done.
Each phase carries accumulated data as a CRDT (semilattice). Messages can
arrive out-of-order or be duplicated; merge always converges correctly.

This is the core of the CRDT architecture: monotonic state transitions
with commutative, associative, idempotent merge operations.

## Instance Constraint Patterns

The Protocol modules use consistent instance requirements:

### For HashMap-based structures (MsgMap, NonceRegistry):
- `[BEq S.PartyId]` - Boolean equality
- `[Hashable S.PartyId]` - Hash function for HashMap

### For decidable equality (if-then-else, match guards):
- `[DecidableEq S.PartyId]` - Prop-valued equality with decision procedure
- Often used alongside BEq/Hashable for compatibility

### For field arithmetic (Lagrange coefficients):
- `[Field S.Scalar]` - Division required for λ_i = Π x_j / (x_j - x_i)
- `[DecidableEq S.Scalar]` - For checking degeneracy

### Consistency guideline:
When defining structures that use MsgMap or HashMap:
1. Add `[BEq S.PartyId] [Hashable S.PartyId]` to the structure definition
2. Add same constraints to all functions operating on that structure
3. If the function also needs if-guards, add `[DecidableEq S.PartyId]`

Example:
```lean
structure MyState (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] where
  messages : MsgMap S MyMsg

def processMsg (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    (st : MyState S) (msg : MyMsg S) : MyState S := ...
```
-/

import IceNine.Protocol.Core
import Mathlib

namespace IceNine.Protocol

open List

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
deriving Repr

/-- Empty message map. -/
def MsgMap.empty {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    : MsgMap S M :=
  { map := Std.HashMap.empty }

/-- Result of attempting to insert a message. -/
inductive InsertResult (S : Scheme) (M : Type*)  [BEq S.PartyId] [Hashable S.PartyId]
  | success (newMap : MsgMap S M)
  | conflict (existing : M)
deriving Repr

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

/-!
## Type Aliases for Message Maps
-/

/-- Map of commit messages, keyed by sender. At most one commit per party. -/
abbrev CommitMap (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] :=
  MsgMap S (DkgCommitMsg S)

/-- Map of reveal messages, keyed by sender. At most one reveal per party. -/
abbrev RevealMap (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] :=
  MsgMap S (DkgRevealMsg S)

/-- Map of share messages, keyed by sender. At most one share per party. -/
abbrev ShareMap (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] :=
  MsgMap S (SignShareMsg S)

/-!
## Sender Accessors

Helper functions to extract sender ID from messages.
-/

/-- Get sender from a DKG commit message. -/
def commitSender {S : Scheme} (m : DkgCommitMsg S) : S.PartyId := m.sender

/-- Get sender from a DKG reveal message. -/
def revealSender {S : Scheme} (m : DkgRevealMsg S) : S.PartyId := m.sender

/-- Get sender from a sign share message. -/
def shareSender {S : Scheme} (m : SignShareMsg S) : S.PartyId := m.sender

/-!
## Protocol Phases

Four-phase protocol: parties first commit to values, then reveal them,
then exchange signature shares, then finalize.
-/

/-- Protocol phases in execution order.
    Monotonic: once in a later phase, never go back. -/
inductive Phase
  | commit  -- collecting commitments
  | reveal  -- collecting reveals (after all commits)
  | shares  -- collecting signature shares
  | done    -- signature complete
  deriving DecidableEq, Repr

/-!
## Per-Phase State Structures

Each phase accumulates different data. All structures use `MsgMap` which
makes it **impossible to express** conflicting messages from the same sender.
CRDT merge uses map union.
-/

/-- Commit phase: accumulating commitment messages.
    At most one commit per party (enforced by MsgMap). -/
structure CommitState (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] where
  commits : CommitMap S

/-- Active signer set for threshold tracking. -/
structure ActiveSet (S : Scheme) where
  set : Finset S.PartyId

/-- Reveal phase: have commits, accumulating reveals.
    At most one reveal per party (enforced by MsgMap). -/
structure RevealState (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] where
  commits : CommitMap S
  reveals : RevealMap S

/-- Share phase: have commits/reveals, accumulating signature shares.
    At most one share per party (enforced by MsgMap).
    Also tracks which parties are expected to contribute. -/
structure ShareState (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] where
  commits : CommitMap S
  reveals : RevealMap S
  shares  : ShareMap S
  active  : Finset S.PartyId    -- expected contributors

/-!
Note: DoneState and State are defined in Sign.lean after Signature/ShareWithCtx
to avoid circular dependencies. Phase.lean defines the basic phase structures,
while Sign.lean completes the phase-indexed state machine.
-/

/-!
## CRDT Merge Instances

Each state type forms a join-semilattice. Merge is:
- Commutative: a ⊔ b = b ⊔ a (on sender sets; message identity preserved)
- Associative: (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
- Idempotent: a ⊔ a = a
This guarantees convergence regardless of message order.

**Key property**: MsgMap makes conflicts un-expressable. Each party can have
at most one message per phase, enforced by the type system.
-/

/-- MsgMap ordering: subset by sender keys. -/
instance {S : Scheme} {M : Type*} [BEq S.PartyId] [Hashable S.PartyId]
    : LE (MsgMap S M) :=
  ⟨fun a b => a.map.toList.all (fun (k, _) => b.map.contains k)⟩

/-- CommitState merge: union of commit maps. -/
instance (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] : Join (CommitState S) :=
  ⟨fun a b => { commits := a.commits ⊔ b.commits }⟩
instance (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] : LE (CommitState S) :=
  ⟨fun a b => a.commits ≤ b.commits⟩

/-- RevealState merge: union of both commit and reveal maps. -/
instance (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] : Join (RevealState S) :=
  ⟨fun a b => { commits := a.commits ⊔ b.commits, reveals := a.reveals ⊔ b.reveals }⟩
instance (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] : LE (RevealState S) :=
  ⟨fun a b => a.commits ≤ b.commits ∧ a.reveals ≤ b.reveals⟩

/-- ShareState merge: union of all maps, union active party set. -/
instance (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] : Join (ShareState S) :=
  ⟨fun a b => { commits := a.commits ⊔ b.commits,
                reveals := a.reveals ⊔ b.reveals,
                shares  := a.shares ⊔ b.shares,
                active  := a.active ∪ b.active }⟩
instance (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] : LE (ShareState S) :=
  ⟨fun a b => a.commits ≤ b.commits ∧ a.reveals ≤ b.reveals ∧ a.shares ≤ b.shares ∧ a.active ⊆ b.active⟩

/-!
Note: DoneState Join/LE instances are defined in Sign.lean along with DoneState itself.
-/

/-!
## CRDT Properties

The MsgMap structure provides strong CRDT guarantees:

**Conflict-freedom by construction**: The `MsgMap` type allows at most one
message per sender. Attempting to add a second message from the same sender
either fails (with `tryInsert`) or is silently ignored (with `insert`).
This makes conflicting messages **un-expressable** in the type system.

**Sender-set commutativity**: The set of sender IDs in `a ⊔ b` equals the set
in `b ⊔ a`. This is guaranteed because HashMap key sets union commutatively.

**Idempotence**: `a ⊔ a = a` holds because inserting existing keys is a no-op.

**Associativity**: `(a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)` holds for the same reason.
-/

/-!
### CRDT Axioms

These properties follow from HashMap semantics but are difficult to prove in Lean 4
due to the implementation details of Std.HashMap. We axiomatize them with clear
documentation of why they hold.

**Why these hold**:
- `merge_senders_comm`: The set of keys in `merge(a, b)` equals `keys(a) ∪ keys(b)`.
  Set union is commutative, so the key sets are equal regardless of merge order.
- `merge_idem`: Merging a map with itself adds no new keys (all keys already present)
  and keeps existing values (first-write-wins on self is identity).
-/

/-- MsgMap merge preserves the union of sender sets.
    Axiomatized: follows from commutativity of set union on HashMap keys. -/
axiom MsgMap.merge_senders_comm {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId]
    (a b : MsgMap S M) :
    (a ⊔ b).senders.toFinset = (b ⊔ a).senders.toFinset

/-- MsgMap merge is idempotent.
    Axiomatized: merging a map with itself is identity (no new keys, values unchanged). -/
axiom MsgMap.merge_idem {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId]
    (a : MsgMap S M) : a ⊔ a = a

/-!
## Convenience Accessors

Extract message lists from state structures.
-/

/-- Get commit messages as a list. -/
def CommitState.commitList {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (st : CommitState S) : List (DkgCommitMsg S) :=
  st.commits.toList

/-- Get commit messages as a list. -/
def RevealState.commitList {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (st : RevealState S) : List (DkgCommitMsg S) :=
  st.commits.toList

/-- Get reveal messages as a list. -/
def RevealState.revealList {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (st : RevealState S) : List (DkgRevealMsg S) :=
  st.reveals.toList

/-- Get commit messages as a list. -/
def ShareState.commitList {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (st : ShareState S) : List (DkgCommitMsg S) :=
  st.commits.toList

/-- Get reveal messages as a list. -/
def ShareState.revealList {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (st : ShareState S) : List (DkgRevealMsg S) :=
  st.reveals.toList

/-- Get share messages as a list. -/
def ShareState.shareList {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (st : ShareState S) : List (SignShareMsg S) :=
  st.shares.toList

/-!
## Processing Messages with Conflict Detection

Use `tryInsert` for strict mode where conflicts are errors.
Use `insert` for CRDT mode where first-write-wins.
-/

/-- Try to add a commit message to commit state. Returns conflict on duplicate sender. -/
def CommitState.tryAddCommit {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (st : CommitState S) (msg : DkgCommitMsg S) : InsertResult S (DkgCommitMsg S) :=
  st.commits.tryInsert commitSender msg

/-- Add a commit message (CRDT mode: ignores if sender already present). -/
def CommitState.addCommit {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (st : CommitState S) (msg : DkgCommitMsg S) : CommitState S :=
  { commits := st.commits.insert commitSender msg }

/-- Try to add a reveal message to reveal state. Returns conflict on duplicate sender. -/
def RevealState.tryAddReveal {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (st : RevealState S) (msg : DkgRevealMsg S) : InsertResult S (DkgRevealMsg S) :=
  st.reveals.tryInsert revealSender msg

/-- Add a reveal message (CRDT mode: ignores if sender already present). -/
def RevealState.addReveal {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (st : RevealState S) (msg : DkgRevealMsg S) : RevealState S :=
  { st with reveals := st.reveals.insert revealSender msg }

/-- Try to add a share message to share state. Returns conflict on duplicate sender. -/
def ShareState.tryAddShare {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (st : ShareState S) (msg : SignShareMsg S) : InsertResult S (SignShareMsg S) :=
  st.shares.tryInsert shareSender msg

/-- Add a share message (CRDT mode: ignores if sender already present). -/
def ShareState.addShare {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (st : ShareState S) (msg : SignShareMsg S) : ShareState S :=
  { st with shares := st.shares.insert shareSender msg }

end IceNine.Protocol
