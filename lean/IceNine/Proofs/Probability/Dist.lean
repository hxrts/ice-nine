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
import Mathlib.Probability.Distributions.Uniform

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

@[ext]
theorem ext (d₁ d₂ : Dist α) (h : ∀ a, d₁.toPMF a = d₂.toPMF a) : d₁ = d₂ := by
  cases d₁ with
  | mk p =>
    cases d₂ with
    | mk q =>
      have : p = q := PMF.ext h
      simp [this]

/-- Point-mass distribution. -/
def pure (a : α) : Dist α :=
  ⟨PMF.pure a⟩

/-- The uniform distribution on a finite, nonempty type. -/
def uniform (α : Type u) [Fintype α] [Nonempty α] : Dist α := by
  classical
  refine ⟨PMF.ofFintype (fun _ : α => (1 : ENNReal) / (Fintype.card α)) ?_⟩
  have hcard : (Fintype.card α : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.2 inferInstance))
  simpa [div_eq_mul_inv, hcard, ENNReal.natCast_ne_top (Fintype.card α)] using
    (ENNReal.mul_inv_cancel (a := (Fintype.card α : ENNReal)) hcard
      (ENNReal.natCast_ne_top (Fintype.card α)))

/-- The uniform distribution supported on a nonempty finset. -/
def uniformFinset (s : Finset α) (hs : s.Nonempty) : Dist α := by
  classical
  exact ⟨PMF.uniformOfFinset s hs⟩

/-- Support of a distribution. -/
def support (d : Dist α) : Set α :=
  d.toPMF.support

/-- Push a distribution forward along a function. -/
def map (f : α → β) (d : Dist α) : Dist β :=
  ⟨d.toPMF.map f⟩

/-- Monadic bind for distributions. -/
def bind (d : Dist α) (f : α → Dist β) : Dist β :=
  ⟨d.toPMF.bind (fun a => (f a).toPMF)⟩


/-- `map` over `pure` is `pure`. -/
theorem map_pure (f : α → β) (a : α) :
    Dist.map f (Dist.pure a) = Dist.pure (f a) := by
  classical
  ext b
  -- Reduce to the `PMF.map_apply` closed form.
  simp [Dist.map, Dist.pure, PMF.map_apply, PMF.pure_apply]
  by_cases hb : b = f a
  · subst hb
    have hfun :
        (fun x : α => if f a = f x then if x = a then (1 : ENNReal) else 0 else 0) =
          fun x : α => if x = a then (1 : ENNReal) else 0 := by
      funext x
      by_cases hx : x = a <;> simp [hx]
    -- The remaining `tsum` is the singleton `a` term.
    simp [hfun, tsum_ite_eq]
  · -- Every summand vanishes (including the `x = a` term) because `b ≠ f a`.
    have hbRhs : (if b = f a then (1 : ENNReal) else 0) = 0 := by
      simp [hb]
    rw [hbRhs]
    refine (ENNReal.tsum_eq_zero).2 ?_
    intro x
    by_cases hx : x = a
    · subst hx
      simp [hb]
    · simp [hx]
/-- `map` commutes with `bind`. -/
theorem map_bind {γ : Type _} (d : Dist α) (f : α → Dist β) (g : β → γ) :
    Dist.map g (Dist.bind d f) = Dist.bind d (fun a => Dist.map g (f a)) := by
  ext c
  simp [Dist.map, Dist.bind, PMF.map_bind]

/-- `bind` after `map` is `bind` with a composed continuation. -/
theorem bind_map {γ : Type _} (d : Dist α) (f : α → β) (g : β → Dist γ) :
    Dist.bind (Dist.map f d) g = Dist.bind d (g ∘ f) := by
  ext c
  simp [Dist.map, Dist.bind, PMF.bind_map]

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


/-! ### Instances -/

instance : Monad Dist where
  pure := fun a => Dist.pure a
  bind := fun d f => Dist.bind d f

/-- A security-parameter-indexed family of distributions. -/
abbrev DistFamily (α : Type u) : Type u :=
  Nat → Dist α

end

end IceNine.Proofs.Probability
