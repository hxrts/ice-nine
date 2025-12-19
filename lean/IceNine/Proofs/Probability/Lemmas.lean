/-
# Probability Layer: Basic Lemmas

Small facts about `Dist.prob` and `StatClose` that we use to transport bounds
through `map`/`bind` and to relate our `prob` definition to mathlib's measure
constructions for `PMF`.
-/

import IceNine.Proofs.Probability.Indistinguishability

set_option autoImplicit false

namespace IceNine.Proofs.Probability

open scoped BigOperators

noncomputable section

namespace Dist

universe u v

variable {α : Type u} {β : Type v}

/-- `Dist.prob` is the same as `PMF.toOuterMeasure` on the underlying `PMF`. -/
theorem prob_eq_toOuterMeasure (d : Dist α) (s : Set α) :
    Dist.prob d s = d.toPMF.toOuterMeasure s := by
  -- `PMF.toOuterMeasure_apply` goes in the opposite direction.
  simpa [Dist.prob] using (PMF.toOuterMeasure_apply (p := d.toPMF) s).symm

theorem prob_singleton (d : Dist α) (a : α) :
    Dist.prob d {a} = d.toPMF a := by
  simpa [prob_eq_toOuterMeasure] using (PMF.toOuterMeasure_apply_singleton (p := d.toPMF) a)

theorem prob_pure_of_mem (a : α) (s : Set α) (ha : a ∈ s) :
    Dist.prob (Dist.pure a) s = 1 := by
  classical
  -- Reduce to `PMF.toOuterMeasure_pure_apply`.
  simp [Dist.pure, prob_eq_toOuterMeasure, ha]

theorem prob_pure_of_notMem (a : α) (s : Set α) (ha : a ∉ s) :
    Dist.prob (Dist.pure a) s = 0 := by
  classical
  simp [Dist.pure, prob_eq_toOuterMeasure, ha]

theorem prob_map_preimage (d : Dist α) (f : α → β) (s : Set β) :
    Dist.prob (Dist.map f d) s = Dist.prob d (f ⁻¹' s) := by
  classical
  -- Use `toOuterMeasure_map_apply` and our bridge lemma.
  simp [Dist.map, prob_eq_toOuterMeasure, PMF.toOuterMeasure_map_apply]

theorem prob_bind (d : Dist α) (f : α → Dist β) (s : Set β) :
    Dist.prob (Dist.bind d f) s = ∑' a, d.toPMF a * Dist.prob (f a) s := by
  classical
  -- `PMF.toOuterMeasure_bind_apply` gives the law of total probability for `PMF.bind`.
  -- We then rewrite `toOuterMeasure` back into `Dist.prob`.
  calc
    Dist.prob (Dist.bind d f) s
        = (d.toPMF.bind (fun a => (f a).toPMF)).toOuterMeasure s := by
            simp [Dist.bind, prob_eq_toOuterMeasure]
    _ = ∑' a, d.toPMF a * (f a).toPMF.toOuterMeasure s := by
          simp
    _ = ∑' a, d.toPMF a * Dist.prob (f a) s := by
          refine tsum_congr fun a => ?_
          simp [prob_eq_toOuterMeasure]

end Dist

namespace StatClose

universe u v

variable {α : Type u} {β : Type v}

/-- Data processing for statistical closeness: pushforward along a function preserves bounds. -/
theorem map {p q : Dist α} {ε : ENNReal} (h : StatClose p q ε) (f : α → β) :
    StatClose (Dist.map f p) (Dist.map f q) ε := by
  intro s
  -- Reduce to the preimage event.
  simpa [Dist.prob_map_preimage] using h (f ⁻¹' s)

end StatClose

end

end IceNine.Proofs.Probability
