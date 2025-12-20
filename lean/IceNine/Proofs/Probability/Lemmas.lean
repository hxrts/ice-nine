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

theorem prob_filter (d : Dist α) (A U : Set α)
    (hA : ∃ a ∈ A, a ∈ d.toPMF.support) :
    Dist.prob (Dist.filter d A hA) U =
      Dist.prob d (U ∩ A) / Dist.prob d A := by
  classical
  -- Expand `PMF.filter` and simplify indicator-on-indicator into an intersection.
  let p : PMF α := d.toPMF
  let c : ENNReal := (∑' a', (A.indicator p) a')⁻¹
  have hind :
      U.indicator (fun a => A.indicator p a * c) = fun a => (U ∩ A).indicator p a * c := by
    funext a
    by_cases haU : a ∈ U <;> by_cases haA : a ∈ A <;>
      simp [Set.indicator, haU, haA, Set.mem_inter_iff]
  calc
    Dist.prob (Dist.filter d A hA) U = ∑' a, U.indicator (p.filter A hA) a := by
      simp [Dist.filter, Dist.prob, p]
    _ = ∑' a, U.indicator (fun a => A.indicator p a * c) a := by
      refine tsum_congr fun a => ?_
      by_cases haU : a ∈ U
      · simp [Set.indicator, haU, PMF.filter_apply, c]
      · simp [Set.indicator, haU]
    _ = ∑' a, ((U ∩ A).indicator p a) * c := by
      simp [hind]
    _ = (∑' a, (U ∩ A).indicator p a) * c := by
      simp [ENNReal.tsum_mul_right]
    _ = Dist.prob d (U ∩ A) / Dist.prob d A := by
      simp [Dist.prob, p, c, div_eq_mul_inv]



theorem prob_ne_top (d : Dist α) (s : Set α) : Dist.prob d s ≠ ⊤ := by
  classical
  simpa [Dist.prob] using (d.toPMF.tsum_coe_indicator_ne_top s)

theorem prob_mono (d : Dist α) {s t : Set α} (h : s ⊆ t) :
    Dist.prob d s ≤ Dist.prob d t := by
  simpa [prob_eq_toOuterMeasure] using (d.toPMF.toOuterMeasure.mono h)

theorem prob_add_prob_compl (d : Dist α) (s : Set α) :
    Dist.prob d s + Dist.prob d sᶜ = 1 := by
  classical
  -- Expand into `tsum` of indicators and use pointwise `indicator + indicatorᶜ = pmf`.
  unfold Dist.prob
  calc
    (∑' a, s.indicator d.toPMF a) + (∑' a, sᶜ.indicator d.toPMF a)
        = ∑' a, (s.indicator d.toPMF a + sᶜ.indicator d.toPMF a) := by
            simpa using
              (ENNReal.tsum_add (f := fun a => s.indicator d.toPMF a)
                (g := fun a => sᶜ.indicator d.toPMF a)).symm
    _ = ∑' a, d.toPMF a := by
          refine tsum_congr (fun a => ?_)
          by_cases ha : a ∈ s <;> simp [Set.indicator, ha]
    _ = 1 := by
          exact d.toPMF.tsum_coe

theorem prob_compl (d : Dist α) (s : Set α) :
    Dist.prob d sᶜ = 1 - Dist.prob d s := by
  have hsum : Dist.prob d s + Dist.prob d sᶜ = 1 := prob_add_prob_compl (d := d) (s := s)
  have htop : Dist.prob d s ≠ ⊤ := prob_ne_top (d := d) (s := s)
  have hsum' : (1 : ENNReal) = Dist.prob d sᶜ + Dist.prob d s := by
    simpa [add_comm, add_left_comm, add_assoc] using hsum.symm
  have : (1 : ENNReal) - Dist.prob d s = Dist.prob d sᶜ :=
    ENNReal.sub_eq_of_eq_add (hb := htop) hsum'
  simpa using this.symm


theorem exists_mem_support_of_prob_ne_zero (d : Dist α) (A : Set α)
    (hA : Dist.prob d A ≠ 0) :
    ∃ a ∈ A, a ∈ d.toPMF.support := by
  classical
  by_contra h
  have hzero : Dist.prob d A = 0 := by
    -- `ENNReal.tsum_eq_zero` characterizes when an `ENNReal` tsum vanishes.
    unfold Dist.prob
    refine (ENNReal.tsum_eq_zero).2 ?_
    intro a
    by_cases ha : a ∈ A
    · have hnot : a ∉ d.toPMF.support := by
        intro hs
        apply h
        exact ⟨a, ha, hs⟩
      have hp0 : d.toPMF a = 0 := by
        -- `a ∉ support` means the mass at `a` is zero.
        simpa [PMF.support] using hnot
      simp [Set.indicator, ha, hp0]
    · simp [Set.indicator, ha]
  exact hA hzero

open scoped Classical in
/-- Probability of an event under the uniform distribution on a nonempty finset.

This is the basic “counting measure” identity:
`Pr[x ∈ U] = |s ∩ U| / |s|` when `x` is uniform on `s`. -/
theorem prob_uniformFinset (s : Finset α) (hs : s.Nonempty) (U : Set α) :
    Dist.prob (Dist.uniformFinset s hs) U =
      ((s.filter fun a => a ∈ U).card : ENNReal) / (s.card : ENNReal) := by
  classical
  -- Bridge through `toOuterMeasure` and use the closed form from mathlib.
  rw [prob_eq_toOuterMeasure]
  simp [Dist.uniformFinset]

end Dist

namespace StatClose

universe u v

variable {α : Type u} {β : Type v}


private theorem div_le_div_add_div_tsub {b c d : ENNReal}
    (hc : c ≤ d) (hb0 : b ≠ 0) (hbt : b ≠ ⊤) (hd0 : d ≠ 0) (hdt : d ≠ ⊤) :
    c / b ≤ c / d + (d - b) / b := by
  -- Cross-multiply by `b`.
  have : c ≤ (c / d + (d - b) / b) * b := by
    -- Expand the RHS.
    simp [add_mul, ENNReal.div_mul_cancel hb0 hbt]
    -- Goal is now `c ≤ c / d * b + (d - b)`.
    -- Rewrite `c` as `(c / d) * d`.
    set t : ENNReal := c / d
    have hcdiv : c = t * d := by
      -- `c / d * d = c`.
      have : c / d * d = c := by
        simpa using (ENNReal.div_mul_cancel (a := d) (b := c) hd0 hdt)
      simpa [t, mul_assoc] using this.symm
    have ht : t ≤ 1 := by
      -- `c / d ≤ 1 ↔ c ≤ d`.
      have : c / d ≤ 1 := (ENNReal.div_le_iff hd0 hdt).2 (by simpa [one_mul] using hc)
      simpa [t] using this
    have hd_le : d ≤ b + (d - b) := by
      -- `d ≤ d - b + b`.
      have := (le_tsub_add (a := b) (b := d))
      simpa [add_comm, add_left_comm, add_assoc] using this
    -- Multiply by `t`.
    have hmul : t * d ≤ t * (b + (d - b)) := by
      exact mul_le_mul_right hd_le t
    -- Expand.
    have hmul' : t * d ≤ t * b + t * (d - b) := by
      simpa [mul_add, add_comm, add_left_comm, add_assoc] using hmul
    -- Bound `t * (d - b)`.
    have htsub : t * (d - b) ≤ d - b := by
      simpa [one_mul] using (mul_le_mul_left ht (d - b))
    have : t * d ≤ t * b + (d - b) := by
      calc
        t * d ≤ t * b + t * (d - b) := hmul'
        _ ≤ t * b + (d - b) := by
          exact add_le_add_right htsub (t * b)
    -- Put back `c`.
    simpa [hcdiv] using this
  exact (ENNReal.div_le_iff hb0 hbt).2 this

theorem filter {p q : Dist α} {ε α0 : ENNReal} (h : StatClose p q ε)
    (A : Set α)
    (hpA : ∃ a ∈ A, a ∈ p.toPMF.support)
    (hqA : ∃ a ∈ A, a ∈ q.toPMF.support)
    (hαp : α0 ≤ Dist.prob p A)
    (hαq : α0 ≤ Dist.prob q A)
    (hα0 : α0 ≠ 0) :
    StatClose (Dist.filter p A hpA) (Dist.filter q A hqA) (2 * ε / α0) := by
  intro U
  -- Rewrite conditioned probabilities.
  simp [Dist.prob_filter]
  -- Shorthand.
  set pU : ENNReal := Dist.prob p (U ∩ A)
  set qU : ENNReal := Dist.prob q (U ∩ A)
  set pA : ENNReal := Dist.prob p A
  set qA : ENNReal := Dist.prob q A
  have hpA0 : pA ≠ 0 := by
    intro hpA0
    have : α0 ≤ 0 := by simpa [pA, hpA0] using hαp
    exact hα0 (by simpa [le_zero_iff] using this)
  have hqA0 : qA ≠ 0 := by
    intro hqA0
    have : α0 ≤ 0 := by simpa [qA, hqA0] using hαq
    exact hα0 (by simpa [le_zero_iff] using this)
  have hpAtop : pA ≠ ⊤ := by
    simpa [pA, Dist.prob] using (p.toPMF.tsum_coe_indicator_ne_top A)
  have hqAtop : qA ≠ ⊤ := by
    simpa [qA, Dist.prob] using (q.toPMF.tsum_coe_indicator_ne_top A)
  have hpU_le : pU ≤ ε + qU := by
    have hmax : max (pU - qU) (qU - pU) ≤ ε := by
      simpa [pU, qU, absSubENNReal] using h (U ∩ A)
    have : pU - qU ≤ ε := le_trans (le_max_left _ _) hmax
    exact (tsub_le_iff_right).1 this
  have hqU_le : qU ≤ ε + pU := by
    have hmax : max (pU - qU) (qU - pU) ≤ ε := by
      simpa [pU, qU, absSubENNReal] using h (U ∩ A)
    have : qU - pU ≤ ε := le_trans (le_max_right _ _) hmax
    exact (tsub_le_iff_right).1 this
  have hpA_le : pA ≤ ε + qA := by
    have hmax : max (pA - qA) (qA - pA) ≤ ε := by
      simpa [pA, qA, absSubENNReal] using h A
    have : pA - qA ≤ ε := le_trans (le_max_left _ _) hmax
    exact (tsub_le_iff_right).1 this
  have hqA_le : qA ≤ ε + pA := by
    have hmax : max (pA - qA) (qA - pA) ≤ ε := by
      simpa [pA, qA, absSubENNReal] using h A
    have : qA - pA ≤ ε := le_trans (le_max_right _ _) hmax
    exact (tsub_le_iff_right).1 this
  have hqU_le_qA : qU ≤ qA := by
    -- monotonicity of `prob`
    have : (U ∩ A) ⊆ A := by intro x hx; exact hx.2
    simpa [qU, qA] using (Dist.prob_mono (d := q) this)
  have hpU_le_pA : pU ≤ pA := by
    have : (U ∩ A) ⊆ A := by intro x hx; exact hx.2
    simpa [pU, pA] using (Dist.prob_mono (d := p) this)
  -- Main bound for `p|A` vs `q|A`.
  have hleft : pU / pA - qU / qA ≤ 2 * ε / α0 := by
    -- First, bound `pU / pA` by `qU / qA` plus `2ε/pA`.
    have hpU_div : pU / pA ≤ (ε + qU) / pA := by
      exact ENNReal.div_le_div_right hpU_le (pA)
    -- Rewrite `(ε + qU) / pA`.
    have : (ε + qU) / pA = ε / pA + qU / pA := by
      simp [ENNReal.add_div]
    -- Compare `qU / pA` with `qU / qA`.
    have hqU_div : qU / pA ≤ qU / qA + (qA - pA) / pA :=
      div_le_div_add_div_tsub (b := pA) (c := qU) (d := qA) hqU_le_qA hpA0 hpAtop hqA0 hqAtop
    have hqA_tsub : (qA - pA) / pA ≤ ε / pA := by
      have : qA - pA ≤ ε := by
        have hmax : max (pA - qA) (qA - pA) ≤ ε := by
          simpa [pA, qA, absSubENNReal] using h A
        exact le_trans (le_max_right _ _) hmax
      exact ENNReal.div_le_div_right this pA
    -- Combine.
    have : pU / pA ≤ qU / qA + (ε / pA + ε / pA) := by
      -- from pU ≤ ε + qU
      have hpU_div' : pU / pA ≤ ε / pA + qU / pA := by
        -- use hpU_le and add_div
        calc
          pU / pA ≤ (ε + qU) / pA := ENNReal.div_le_div_right hpU_le pA
          _ = ε / pA + qU / pA := by simp [ENNReal.add_div]
      have : ε / pA + qU / pA ≤ ε / pA + (qU / qA + (qA - pA) / pA) := by
        exact add_le_add_right hqU_div (ε / pA)
      have : ε / pA + qU / pA ≤ ε / pA + (qU / qA + ε / pA) := by
        calc
          ε / pA + qU / pA ≤ ε / pA + (qU / qA + (qA - pA) / pA) := this
          _ ≤ ε / pA + (qU / qA + ε / pA) := by
              have hinner : qU / qA + (qA - pA) / pA ≤ qU / qA + ε / pA := by
                exact add_le_add_right hqA_tsub (qU / qA)
              exact add_le_add_right hinner (ε / pA)
      -- rearrange
      calc
        pU / pA ≤ ε / pA + qU / pA := hpU_div'
        _ ≤ ε / pA + (qU / qA + ε / pA) := this
        _ = qU / qA + (ε / pA + ε / pA) := by
              simp [add_assoc, add_comm]
    -- Convert to a `tsub` bound.
    have : pU / pA - qU / qA ≤ (ε / pA + ε / pA) := by
      exact (tsub_le_iff_right).2 (by simpa [add_comm, add_left_comm, add_assoc] using this)
    -- Now bound `ε/pA` by `ε/α0`.
    have hinv : pA⁻¹ ≤ α0⁻¹ := by
      -- inv is order-reversing
      exact (ENNReal.inv_le_inv).2 hαp
    have hεdiv : ε / pA ≤ ε / α0 := by
      -- ε * pA⁻¹ ≤ ε * α0⁻¹
      simpa [div_eq_mul_inv] using mul_le_mul_right hinv ε
    have hsum : ε / pA + ε / pA ≤ ε / α0 + ε / α0 := by
      exact add_le_add hεdiv hεdiv
    -- finish
    have : pU / pA - qU / qA ≤ ε / α0 + ε / α0 := le_trans this hsum
    have htwo : ε / α0 + ε / α0 = 2 * ε / α0 := by
      simp [two_mul, ENNReal.add_div]
    simpa [htwo] using this
  -- Symmetric bound.
  have hright : qU / qA - pU / pA ≤ 2 * ε / α0 := by
    -- repeat with p/q swapped
    have hpU_div : qU / qA ≤ (ε + pU) / qA := by
      exact ENNReal.div_le_div_right hqU_le qA
    have hpU_div' : qU / qA ≤ ε / qA + pU / qA := by
      calc
        qU / qA ≤ (ε + pU) / qA := ENNReal.div_le_div_right hqU_le qA
        _ = ε / qA + pU / qA := by simp [ENNReal.add_div]
    have hpU_div2 : pU / qA ≤ pU / pA + (pA - qA) / qA :=
      div_le_div_add_div_tsub (b := qA) (c := pU) (d := pA) hpU_le_pA hqA0 hqAtop hpA0 hpAtop
    have hpA_tsub : (pA - qA) / qA ≤ ε / qA := by
      have : pA - qA ≤ ε := by
        have hmax : max (pA - qA) (qA - pA) ≤ ε := by
          simpa [pA, qA, absSubENNReal] using h A
        exact le_trans (le_max_left _ _) hmax
      exact ENNReal.div_le_div_right this qA
    have : qU / qA ≤ pU / pA + (ε / qA + ε / qA) := by
      have : ε / qA + pU / qA ≤ ε / qA + (pU / pA + (pA - qA) / qA) := by
        exact add_le_add_right hpU_div2 (ε / qA)
      have : ε / qA + pU / qA ≤ ε / qA + (pU / pA + ε / qA) := by
        calc
          ε / qA + pU / qA ≤ ε / qA + (pU / pA + (pA - qA) / qA) := this
          _ ≤ ε / qA + (pU / pA + ε / qA) := by
              have hinner : pU / pA + (pA - qA) / qA ≤ pU / pA + ε / qA := by
                exact add_le_add_right hpA_tsub (pU / pA)
              exact add_le_add_right hinner (ε / qA)
      calc
        qU / qA ≤ ε / qA + pU / qA := hpU_div'
        _ ≤ ε / qA + (pU / pA + ε / qA) := this
        _ = pU / pA + (ε / qA + ε / qA) := by
          -- reassociate and commute
          calc
            ε / qA + (pU / pA + ε / qA)
                = ε / qA + pU / pA + ε / qA := by simp [add_assoc]
            _ = pU / pA + ε / qA + ε / qA := by
                  simp [add_comm, add_left_comm]
            _ = pU / pA + (ε / qA + ε / qA) := by simp [add_assoc]
    have : qU / qA - pU / pA ≤ ε / qA + ε / qA :=
      (tsub_le_iff_right).2 (by simpa [add_comm, add_left_comm, add_assoc] using this)
    have hinv : qA⁻¹ ≤ α0⁻¹ := (ENNReal.inv_le_inv).2 hαq
    have hεdiv : ε / qA ≤ ε / α0 := by
      simpa [div_eq_mul_inv] using mul_le_mul_right hinv ε
    have hsum : ε / qA + ε / qA ≤ ε / α0 + ε / α0 := add_le_add hεdiv hεdiv
    have : qU / qA - pU / pA ≤ ε / α0 + ε / α0 := le_trans this hsum
    have htwo : ε / α0 + ε / α0 = 2 * ε / α0 := by
      simp [two_mul, ENNReal.add_div]
    simpa [htwo] using this
  -- Wrap into `absSubENNReal`.
  -- `absSubENNReal` is a `max` of the two one-sided bounds.
  simpa [absSubENNReal, max_le_iff] using (show max (pU / pA - qU / qA) (qU / qA - pU / pA) ≤ 2 * ε / α0 from
    (max_le_iff).2 ⟨hleft, hright⟩)


/-- Mixtures preserve statistical closeness: if each branch is close with error `ε`, then
combining them with a fixed outer distribution preserves the same error. -/
theorem bind {p : Dist α} {f g : α → Dist β} {ε : ENNReal}
    (h : ∀ a, StatClose (f a) (g a) ε) :
    StatClose (Dist.bind p f) (Dist.bind p g) ε := by
  intro s
  have hle : Dist.prob (Dist.bind p f) s ≤ Dist.prob (Dist.bind p g) s + ε := by
    have hpoint : ∀ a, Dist.prob (f a) s ≤ Dist.prob (g a) s + ε := by
      intro a
      have hmax : max (Dist.prob (f a) s - Dist.prob (g a) s)
          (Dist.prob (g a) s - Dist.prob (f a) s) ≤ ε := by
        simpa [absSubENNReal] using h a s
      have : Dist.prob (f a) s - Dist.prob (g a) s ≤ ε := le_trans (le_max_left _ _) hmax
      exact (tsub_le_iff_left).1 this
    calc
      Dist.prob (Dist.bind p f) s = ∑' a, p.toPMF a * Dist.prob (f a) s := by
        simp [Dist.prob_bind]
      _ ≤ ∑' a, p.toPMF a * (Dist.prob (g a) s + ε) := by
        refine ENNReal.tsum_le_tsum ?_
        intro a
        exact mul_le_mul_right (hpoint a) (p.toPMF a)
      _ = ∑' a, (p.toPMF a * Dist.prob (g a) s + p.toPMF a * ε) := by
        simp [mul_add]
      _ = (∑' a, p.toPMF a * Dist.prob (g a) s) + ∑' a, p.toPMF a * ε := by
        simp [ENNReal.tsum_add]
      _ = Dist.prob (Dist.bind p g) s + ε := by
        simp [Dist.prob_bind, ENNReal.tsum_mul_right]
  have hge : Dist.prob (Dist.bind p g) s ≤ Dist.prob (Dist.bind p f) s + ε := by
    have hpoint : ∀ a, Dist.prob (g a) s ≤ Dist.prob (f a) s + ε := by
      intro a
      have hmax : max (Dist.prob (f a) s - Dist.prob (g a) s)
          (Dist.prob (g a) s - Dist.prob (f a) s) ≤ ε := by
        simpa [absSubENNReal] using h a s
      have : Dist.prob (g a) s - Dist.prob (f a) s ≤ ε := le_trans (le_max_right _ _) hmax
      exact (tsub_le_iff_left).1 this
    calc
      Dist.prob (Dist.bind p g) s = ∑' a, p.toPMF a * Dist.prob (g a) s := by
        simp [Dist.prob_bind]
      _ ≤ ∑' a, p.toPMF a * (Dist.prob (f a) s + ε) := by
        refine ENNReal.tsum_le_tsum ?_
        intro a
        exact mul_le_mul_right (hpoint a) (p.toPMF a)
      _ = ∑' a, (p.toPMF a * Dist.prob (f a) s + p.toPMF a * ε) := by
        simp [mul_add]
      _ = (∑' a, p.toPMF a * Dist.prob (f a) s) + ∑' a, p.toPMF a * ε := by
        simp [ENNReal.tsum_add]
      _ = Dist.prob (Dist.bind p f) s + ε := by
        simp [Dist.prob_bind, ENNReal.tsum_mul_right]
  have hsub : Dist.prob (Dist.bind p f) s - Dist.prob (Dist.bind p g) s ≤ ε :=
    (tsub_le_iff_left).2 hle
  have hsub' : Dist.prob (Dist.bind p g) s - Dist.prob (Dist.bind p f) s ≤ ε :=
    (tsub_le_iff_left).2 hge
  -- Wrap into `absSubENNReal`.
  simpa [absSubENNReal, max_le_iff] using And.intro hsub hsub'

/-- Data processing for statistical closeness: pushforward along a function preserves bounds. -/
theorem map {p q : Dist α} {ε : ENNReal} (h : StatClose p q ε) (f : α → β) :
    StatClose (Dist.map f p) (Dist.map f q) ε := by
  intro s
  -- Reduce to the preimage event.
  simpa [Dist.prob_map_preimage] using h (f ⁻¹' s)

end StatClose

namespace Indistinguishable

universe u

variable {α : Type u}

/-- Data processing for indistinguishability: pushforward along a function preserves bounds. -/
theorem map {β : Type*} (D₁ D₂ : DistFamily α) (f : α → β)
    (h : Indistinguishable D₁ D₂) :
    Indistinguishable (fun κ => Dist.map f (D₁ κ)) (fun κ => Dist.map f (D₂ κ)) := by
  rcases h with ⟨ε, hεneg, hεclose⟩
  refine ⟨ε, hεneg, ?_⟩
  intro κ
  exact StatClose.map (h := hεclose κ) f

/-- Conditioning preserves indistinguishability up to a `1/Pr[A]` blowup, assuming a uniform
lower bound `α0` on acceptance probability in both worlds. -/
theorem filter_const (D₁ D₂ : DistFamily α) (A : Set α) (α0 : ENNReal)
    (h : Indistinguishable D₁ D₂)
    (hA₁ : ∀ κ, ∃ a ∈ A, a ∈ (D₁ κ).toPMF.support)
    (hA₂ : ∀ κ, ∃ a ∈ A, a ∈ (D₂ κ).toPMF.support)
    (hα0 : α0 ≠ 0)
    (hprob₁ : ∀ κ, α0 ≤ Dist.prob (D₁ κ) A)
    (hprob₂ : ∀ κ, α0 ≤ Dist.prob (D₂ κ) A) :
    Indistinguishable (fun κ => Dist.filter (D₁ κ) A (hA₁ κ))
      (fun κ => Dist.filter (D₂ κ) A (hA₂ κ)) := by
  rcases h with ⟨ε, hεneg, hεclose⟩
  refine ⟨fun κ => 2 * ε κ / α0, ?_, ?_⟩
  · -- Negligible scaling by a finite constant.
    have hcinv : α0⁻¹ ≠ ⊤ := (ENNReal.inv_ne_top).2 hα0
    have hc : (2 / α0) ≠ ⊤ := by
      have h2 : (2 : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top 2
      simpa [div_eq_mul_inv] using ENNReal.mul_ne_top h2 hcinv
    have hmul : Negligible (fun κ => ε κ * (2 / α0)) :=
      Negligible.mul_const hεneg (2 / α0) hc
    -- Rewrite `ε κ * (2/α0)` into `2 * ε κ / α0`.
    unfold Negligible at hmul ⊢
    refine Asymptotics.SuperpolynomialDecay.congr hmul ?_
    intro κ
    simp [div_eq_mul_inv, mul_left_comm, mul_comm]
  · intro κ
    -- Pointwise: conditioning amplifies statistical distance by at most `2/α0`.
    exact StatClose.filter (h := hεclose κ) (A := A) (hpA := hA₁ κ) (hqA := hA₂ κ)
      (hαp := hprob₁ κ) (hαq := hprob₂ κ) (hα0 := hα0)

end Indistinguishable

end

end IceNine.Proofs.Probability
