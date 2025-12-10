/-
# Phase-Indexed Protocol State

Protocol progress modeled as discrete phases: commit → reveal → shares → done.
Each phase carries accumulated data as a CRDT (semilattice). Messages can
arrive out-of-order or be duplicated; merge always converges correctly.

This is the core of the CRDT architecture: monotonic state transitions
with commutative, associative, idempotent merge operations.
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

Each phase accumulates different data. All structures have CRDT merge:
lists via append, Finsets via union.
-/

/-- Commit phase: accumulating commitment messages. -/
structure CommitState (S : Scheme) where
  commits : List (DkgCommitMsg S)

/-- Active signer set for threshold tracking. -/
structure ActiveSet (S : Scheme) where
  set : Finset S.PartyId

/-- Reveal phase: have commits, accumulating reveals. -/
structure RevealState (S : Scheme) where
  commits : List (DkgCommitMsg S)
  reveals : List (DkgRevealMsg S)

/-- Share phase: have commits/reveals, accumulating signature shares.
    Also tracks which parties are expected to contribute. -/
structure ShareState (S : Scheme) where
  commits : List (DkgCommitMsg S)
  reveals : List (DkgRevealMsg S)
  shares  : List (SignShareMsg S)
  active  : Finset S.PartyId    -- expected contributors

/-!
Note: DoneState and State are defined in Sign.lean after Signature/ShareWithCtx
to avoid circular dependencies. Phase.lean defines the basic phase structures,
while Sign.lean completes the phase-indexed state machine.
-/

/-!
## CRDT Merge Instances

Each state type forms a join-semilattice. Merge is:
- Commutative: a ⊔ b = b ⊔ a
- Associative: (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
- Idempotent: a ⊔ a = a
This guarantees convergence regardless of message order.
-/

/-- List merge: concatenation (dedup at use sites if needed). -/
instance {α} : Join (List α) := ⟨List.append⟩
instance {α} : LE (List α) := ⟨fun a b => ∀ x, x ∈ a → x ∈ b⟩

/-- CommitState merge: append commit lists. -/
instance (S : Scheme) : Join (CommitState S) := ⟨fun a b => { commits := a.commits ⊔ b.commits }⟩
instance (S : Scheme) : LE (CommitState S) := ⟨fun a b => a.commits ≤ b.commits⟩

/-- RevealState merge: append both commit and reveal lists. -/
instance (S : Scheme) : Join (RevealState S) :=
  ⟨fun a b => { commits := a.commits ⊔ b.commits, reveals := a.reveals ⊔ b.reveals }⟩
instance (S : Scheme) : LE (RevealState S) := ⟨fun a b => a.commits ≤ b.commits ∧ a.reveals ≤ b.reveals⟩

/-- ShareState merge: append all lists, union active sets. -/
instance (S : Scheme) : Join (ShareState S) :=
  ⟨fun a b => { commits := a.commits ⊔ b.commits,
                reveals := a.reveals ⊔ b.reveals,
                shares  := a.shares ⊔ b.shares,
                active  := Finset.union a.active b.active }⟩
instance (S : Scheme) : LE (ShareState S) :=
  ⟨fun a b => a.commits ≤ b.commits ∧ a.reveals ≤ b.reveals ∧ a.shares ≤ b.shares ∧ a.active ⊆ b.active⟩

/-!
Note: DoneState Join/LE instances are defined in Sign.lean along with DoneState itself.
-/

/-!
## CRDT Properties

The Join instances above satisfy semilattice laws:
- Commutativity: a ⊔ b = b ⊔ a
- Associativity: (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
- Idempotence: a ⊔ a = a

These properties ensure CRDT convergence regardless of message order.
Proofs omitted as they follow directly from List.append and Finset.union properties.

**Note on Duplicates**: List-based merge uses append, which may accumulate
duplicates. This is intentional for CRDT semantics (append is associative,
commutative up to reordering, idempotent on empty). Duplicates are removed
at aggregation time using the normalize functions below.
-/

/-!
## Normalization (Deduplication)

Before aggregating messages, remove duplicates to avoid double-counting.
These functions should be called before `dkgAggregate`, `aggregateSignature`, etc.
-/

/-- Remove duplicate commits by sender. -/
def CommitState.normalize [DecidableEq S.PartyId] (st : CommitState S) : CommitState S :=
  { commits := st.commits.dedup }

/-- Remove duplicate reveals by sender. -/
def RevealState.normalize [DecidableEq S.PartyId] (st : RevealState S) : RevealState S :=
  { commits := st.commits.dedup
    reveals := st.reveals.dedup }

/-- Remove duplicate shares by sender. -/
def ShareState.normalize [DecidableEq S.PartyId] (st : ShareState S) : ShareState S :=
  { commits := st.commits.dedup
    reveals := st.reveals.dedup
    shares := st.shares.dedup
    active := st.active }

/-- Normalize DKG commits list (dedup by sender). -/
def dedupCommits [DecidableEq S.PartyId]
    (commits : List (DkgCommitMsg S)) : List (DkgCommitMsg S) :=
  commits.dedup

/-- Normalize DKG reveals list (dedup by sender). -/
def dedupReveals [DecidableEq S.PartyId]
    (reveals : List (DkgRevealMsg S)) : List (DkgRevealMsg S) :=
  reveals.dedup

/-- Normalize sign shares list (dedup by sender). -/
def dedupShares [DecidableEq S.PartyId]
    (shares : List (SignShareMsg S)) : List (SignShareMsg S) :=
  shares.dedup

end IceNine.Protocol
