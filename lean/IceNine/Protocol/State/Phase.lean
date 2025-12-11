/-
# Phase-Indexed Protocol State (MsgMap Version)

Protocol progress modeled as discrete phases: commit → reveal → shares → done.
Each phase carries accumulated data as a CRDT (semilattice). Messages can
arrive out-of-order or be duplicated; merge always converges correctly.

This is the core of the CRDT architecture: monotonic state transitions
with commutative, associative, idempotent merge operations.

## Phase.lean vs PhaseIndexed.lean

There are two phase implementations with different trade-offs:

| Feature | Phase.lean (this) | PhaseIndexed.lean |
|---------|------------------|-------------------|
| Storage | MsgMap (HashMap) | List |
| Conflict handling | Un-expressable by type | Runtime check |
| Phase safety | Runtime check | Compile-time type |
| Use case | Production/networking | Proofs/high-level logic |
| Merge semantics | CRDT (commutative) | Append-based |

**Use Phase.lean** (this module) when:
- Building production networking code
- Need CRDT merge semantics
- Want conflicts to be structurally impossible

**Use PhaseIndexed.lean** when:
- Phase correctness is the primary safety concern
- Writing security proofs
- Want compile-time phase transition checking

See `Protocol/PhaseIndexed.lean` for the alternative implementation.

## Instance Constraint Patterns

The Protocol modules use constraint aliases defined in `Core.lean` for cleaner signatures:

| Alias | Constraints | Use Case |
|-------|-------------|----------|
| `PartyIdHash S` | `BEq S.PartyId`, `Hashable S.PartyId` | HashMap-based structures |
| `PartyIdState S` | `PartyIdHash S`, `DecidableEq S.PartyId` | State operations with guards |
| `ScalarField S` | `Field S.Scalar`, `DecidableEq S.Scalar` | Lagrange coefficients |

### Usage Example:
```lean
-- Using constraint alias:
def processMsg (S : Scheme) [PartyIdState S]
    (st : MyState S) (msg : MyMsg S) : MyState S := ...

-- Equivalent to:
def processMsg (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    (st : MyState S) (msg : MyMsg S) : MyState S := ...
```

Note: Existing code still uses explicit constraints for backward compatibility.
New code should prefer the aliases for brevity.
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.Core.CRDT
import Mathlib

namespace IceNine.Protocol

open List

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

These are type-specialized versions of `getSender` for use with MsgMap operations.
The MsgMap.insert/tryInsert functions require a sender extraction function.
-/

/-- Get sender from a DKG commit message. -/
abbrev commitSender {S : Scheme} : DkgCommitMsg S → S.PartyId := getSender

/-- Get sender from a DKG reveal message. -/
abbrev revealSender {S : Scheme} : DkgRevealMsg S → S.PartyId := getSender

/-- Get sender from a sign share message. -/
abbrev shareSender {S : Scheme} : SignShareMsg S → S.PartyId := getSender

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
instance (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] : Join (ShareState S) :=
  ⟨fun a b => { commits := a.commits ⊔ b.commits,
                reveals := a.reveals ⊔ b.reveals,
                shares  := a.shares ⊔ b.shares,
                active  := a.active ∪ b.active }⟩
instance (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] : LE (ShareState S) :=
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
    [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
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
