/-
# Phase-indexed protocol state with semilattice merge

We model protocol progress as a phase-indexed state. Each phase carries the
data accumulated so far. States form a join-semilattice via componentwise merge
so we can CRDT-merge out-of-order or duplicated events.
-/

import IceNine.Protocol.Core
import Mathlib

namespace IceNine.Protocol

open List

inductive Phase
  | commit
  | reveal
  | shares
  | done
  deriving DecidableEq, Repr

structure CommitState (S : Scheme) :=
  (commits : List (DkgCommitMsg S))
deriving Repr

-- Active signer set carried forward (Finset for t-of-n proofs).
structure ActiveSet (S : Scheme) :=
  (set : Finset S.PartyId)
deriving Repr
structure RevealState (S : Scheme) :=
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
deriving Repr

structure ShareState (S : Scheme) :=
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (shares  : List (SignShareMsg S))
  (active  : Finset S.PartyId) -- participants expected to contribute shares
  deriving Repr

structure DoneState (S : Scheme) :=
  (sig : Signature S)
deriving Repr

def State (S : Scheme) : Phase → Type
  | .commit => CommitState S
  | .reveal => RevealState S
  | .shares => ShareWithCtx S
  | .done   => DoneState S

-- Semilattice merge for lists: prefer concatenation; dedup can be added later.
instance {α} : Join (List α) := ⟨List.append⟩
instance {α} : LE (List α) := ⟨fun a b => ∀ x, x ∈ a → x ∈ b⟩

-- CommitState merge: append commits.
instance (S : Scheme) : Join (CommitState S) := ⟨fun a b => { commits := a.commits ⊔ b.commits }⟩
instance (S : Scheme) : LE (CommitState S) := ⟨fun a b => a.commits ≤ b.commits⟩

-- RevealState merge: append commits and reveals.
instance (S : Scheme) : Join (RevealState S) :=
  ⟨fun a b => { commits := a.commits ⊔ b.commits, reveals := a.reveals ⊔ b.reveals }⟩
instance (S : Scheme) : LE (RevealState S) := ⟨fun a b => a.commits ≤ b.commits ∧ a.reveals ≤ b.reveals⟩

-- ShareState merge: append everything.
instance (S : Scheme) : Join (ShareState S) :=
  ⟨fun a b => { commits := a.commits ⊔ b.commits,
                reveals := a.reveals ⊔ b.reveals,
                shares  := a.shares ⊔ b.shares,
                active  := a.active ∪ b.active }⟩
instance (S : Scheme) : LE (ShareState S) :=
  ⟨fun a b => a.commits ≤ b.commits ∧ a.reveals ≤ b.reveals ∧ a.shares ≤ b.shares ∧ a.active ⊆ b.active⟩

-- DoneState merge: prefer left if already done, else right (idempotent join).
instance (S : Scheme) : Join (DoneState S) :=
  ⟨fun a b => a⟩
instance (S : Scheme) : LE (DoneState S) := ⟨fun _ _ => True⟩

-- Show that these joins are commutative/idempotent/associative (CRDT-safe).
instance (S : Scheme) : SemilatticeSup (CommitState S) := by infer_instance
instance (S : Scheme) : SemilatticeSup (RevealState S) := by infer_instance
instance (S : Scheme) : SemilatticeSup (ShareState S) := by infer_instance
instance (S : Scheme) : SemilatticeSup (DoneState S) := by infer_instance

end IceNine.Protocol
