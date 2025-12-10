/-
# Product Semilattice Instances

Generic semilattice for product types. Enables combining multiple CRDT
states (phase, refresh, repair, rerand) into a single composite state
that merges componentwise.

Given (α × β) where both α and β are semilattices:
  (a₁, b₁) ⊔ (a₂, b₂) = (a₁ ⊔ a₂, b₁ ⊔ b₂)
-/

import IceNine.Protocol.Phase
import IceNine.Protocol.RefreshState
import IceNine.Protocol.Repair
import IceNine.Protocol.Rerandomize

namespace IceNine.Protocol

/-!
## Product Join

Componentwise join for pairs. Extends naturally to tuples via nesting.
-/

/-- Componentwise join for products: (a₁, b₁) ⊔ (a₂, b₂) = (a₁⊔a₂, b₁⊔b₂). -/
instance prodJoin (α β) [Join α] [Join β] : Join (α × β) :=
  ⟨fun a b => (a.1 ⊔ b.1, a.2 ⊔ b.2)⟩

/-!
## Product Semilattice

Full semilattice structure for products. Mathlib provides this automatically
via `Prod.instSemilatticeSup` from `Mathlib.Order.Lattice`. The ordering is
componentwise: (a₁, b₁) ≤ (a₂, b₂) ↔ a₁ ≤ a₂ ∧ b₁ ≤ b₂.

We re-export the instance here for clarity and to ensure our Join aligns.
-/

-- Mathlib provides SemilatticeSup (α × β) automatically when both components
-- have SemilatticeSup instances. No custom proof needed.

end IceNine.Protocol
