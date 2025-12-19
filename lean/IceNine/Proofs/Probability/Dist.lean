/-
# Probability Layer: Distributions

This module introduces a probability layer for IceNine proofs.

We intentionally keep `Dist` abstract from the perspective of the rest of the
codebase by wrapping mathlib's `PMF`. This allows us to later swap the concrete
probability model (e.g. to `Measure`) without rewriting every proof.

The key construction we rely on immediately is conditioning (`filter`), which
models rejection sampling.
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit false

namespace IceNine.Proofs.Probability

open scoped BigOperators

noncomputable section

universe u v

/-- A discrete distribution over `α`.

Implementation note: this is currently backed by `PMF α`, but we keep it behind
this wrapper so that the rest of IceNine does not mention `PMF` directly. -/
structure Dist (α : Type u) where
  toPMF : PMF α

namespace Dist

variable {α : Type u} {β : Type v}

instance : Coe (Dist α) (PMF α) :=
  ⟨Dist.toPMF⟩

/-- The uniform distribution on a finite, nonempty type. -/
def uniform (α : Type u) [Fintype α] [Nonempty α] : Dist α := by
  classical
  refine ⟨PMF.ofFintype (fun _ : α => (1 : ENNReal) / (Fintype.card α)) ?_⟩
  have hcard : (Fintype.card α : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.2 inferInstance))
  simpa [div_eq_mul_inv, hcard, ENNReal.natCast_ne_top (Fintype.card α)] using
    (ENNReal.mul_inv_cancel (a := (Fintype.card α : ENNReal)) hcard
      (ENNReal.natCast_ne_top (Fintype.card α)))

/-- Support of a distribution. -/
def support (d : Dist α) : Set α :=
  d.toPMF.support

/-- Push a distribution forward along a function. -/
def map (f : α → β) (d : Dist α) : Dist β :=
  ⟨d.toPMF.map f⟩

/-- Monadic bind for distributions. -/
def bind (d : Dist α) (f : α → Dist β) : Dist β :=
  ⟨d.toPMF.bind (fun a => (f a).toPMF)⟩

/-- Product of independent distributions. -/
def prod (da : Dist α) (db : Dist β) : Dist (α × β) :=
  da.bind (fun a => db.map (fun b => (a, b)))

/-- Probability of an event (as a set). -/
def prob (d : Dist α) (s : Set α) : ENNReal :=
  ∑' a, s.indicator d.toPMF a

/-- Condition a distribution on a set with nonzero probability mass. -/
def filter (d : Dist α) (s : Set α) (h : ∃ a ∈ s, a ∈ d.toPMF.support) : Dist α :=
  ⟨d.toPMF.filter s h⟩

end Dist

/-- A security-parameter-indexed family of distributions. -/
abbrev DistFamily (α : Type u) : Type u :=
  Nat → Dist α

end

end IceNine.Proofs.Probability
