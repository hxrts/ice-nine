/-
# Combined CRDT states

Simple product semilattice instances to combine protocol phase state with
refresh/repair/rerandomization metadata.
-/

import IceNine.Protocol.Phase
import IceNine.Protocol.RefreshState
import IceNine.Protocol.Repair
import IceNine.Protocol.Rerandomize

namespace IceNine.Protocol

instance prodJoin (α β) [Join α] [Join β] : Join (α × β) :=
  ⟨fun a b => (a.1 ⊔ b.1, a.2 ⊔ b.2)⟩

instance prodSemilatticeSup (α β) [SemilatticeSup α] [SemilatticeSup β] : SemilatticeSup (α × β) := by
  classical
  refine
    { sup := (· ⊔ ·)
      le := fun a b => a.1 ≤ b.1 ∧ a.2 ≤ b.2
      le_sup_left := ?_
      le_sup_right := ?_
      sup_le := ?_
      sup_assoc := ?_
      sup_comm := ?_
      le_refl := by intro a; constructor <;> exact le_rfl
      le_trans := ?_ } <;> intros <;> constructor <;> simp [sup_assoc, sup_comm, sup_left_comm, prodJoin] <;> tauto

end IceNine.Protocol
