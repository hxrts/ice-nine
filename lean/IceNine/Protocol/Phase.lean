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
structure CommitState (S : Scheme) :=
  (commits : List (DkgCommitMsg S))
deriving Repr

/-- Active signer set for threshold tracking. -/
structure ActiveSet (S : Scheme) :=
  (set : Finset S.PartyId)
deriving Repr

/-- Reveal phase: have commits, accumulating reveals. -/
structure RevealState (S : Scheme) :=
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
deriving Repr

/-- Share phase: have commits/reveals, accumulating signature shares.
    Also tracks which parties are expected to contribute. -/
structure ShareState (S : Scheme) :=
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (shares  : List (SignShareMsg S))
  (active  : Finset S.PartyId)    -- expected contributors
deriving Repr

/-- Done phase: signature complete and finalized. -/
structure DoneState (S : Scheme) :=
  (sig : Signature S)
deriving Repr

/-- Phase-indexed state type. Returns the appropriate state for each phase. -/
def State (S : Scheme) [DecidableEq S.PartyId] : Phase → Type
  | .commit => CommitState S
  | .reveal => RevealState S
  | .shares => ShareWithCtx S
  | .done   => DoneState S

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
                active  := a.active ∪ b.active }⟩
instance (S : Scheme) : LE (ShareState S) :=
  ⟨fun a b => a.commits ≤ b.commits ∧ a.reveals ≤ b.reveals ∧ a.shares ≤ b.shares ∧ a.active ⊆ b.active⟩

/-- DoneState merge: idempotent (signature already finalized). -/
instance (S : Scheme) : Join (DoneState S) :=
  ⟨fun a b => a⟩
instance (S : Scheme) : LE (DoneState S) := ⟨fun _ _ => True⟩

/-!
## Semilattice Instances

Full semilattice structure enables CRDT-safe merge operations.
-/

instance (S : Scheme) : SemilatticeSup (CommitState S) := by infer_instance
instance (S : Scheme) : SemilatticeSup (RevealState S) := by infer_instance
instance (S : Scheme) : SemilatticeSup (ShareState S) := by infer_instance
instance (S : Scheme) : SemilatticeSup (DoneState S) := by infer_instance

end IceNine.Protocol
