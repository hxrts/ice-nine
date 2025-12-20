/-
# Probability Layer: Centered-Bounded Shift Bounds

This file proves basic *statistical* bounds for centered-bounded sampling.

Core idea:
- `CenteredBounded.int B` is uniform on the finite interval `[-B, B]`.
- Shifting that interval by `δ` changes membership of at most `|δ|` points.
- For vectors `Fin n → Int`, we treat the box `[-B, B]^n` as a product of `n`
  intervals and apply a simple union bound to get a `∑ |δ i|` estimate.
-/

import IceNine.Proofs.Probability.CenteredBounded
import IceNine.Proofs.Probability.IntervalShift
import IceNine.Proofs.Probability.Lemmas
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

namespace IceNine.Proofs.Probability

open scoped BigOperators

noncomputable section

namespace CenteredBounded

open Finset

/-- Shift the interval `[-B, B]` by `δ` (as a finset). -/
def shiftedInterval (B : Nat) (δ : Int) : Finset Int :=
  Finset.Icc (-(B : Int) + δ) ((B : Int) + δ)

/-- The centered box `[-B, B]^n` as a finset. -/
def box (n B : Nat) : Finset (Fin n → Int) :=
  Fintype.piFinset (fun _ : Fin n => interval B)

/-- Shift the centered box `[-B, B]^n` coordinatewise by `δ` (as a finset). -/
def shiftedBox (n B : Nat) (δ : Fin n → Int) : Finset (Fin n → Int) :=
  Fintype.piFinset (fun i : Fin n => shiftedInterval B (δ i))

theorem shiftedInterval_nonempty (B : Nat) (δ : Int) : (shiftedInterval B δ).Nonempty := by
  have hB : (0 : Int) ≤ (B : Int) := by
    exact_mod_cast (Nat.zero_le B)
  have h : (-(B : Int) + δ) ≤ ((B : Int) + δ) := by
    linarith [neg_le_self hB]
  dsimp [shiftedInterval]
  exact Finset.nonempty_Icc.2 h

theorem box_nonempty (n B : Nat) : (box n B).Nonempty := by
  simpa [box] using (interval_nonempty B).piFinset_const (ι := Fin n)

theorem shiftedBox_nonempty (n B : Nat) (δ : Fin n → Int) : (shiftedBox n B δ).Nonempty := by
  classical
  simpa [shiftedBox] using (Fintype.piFinset_nonempty.2 fun i => shiftedInterval_nonempty B (δ i))

theorem mem_box_iff (n B : Nat) (x : Fin n → Int) :
    x ∈ box n B ↔ ∀ i, x i ∈ interval B := by
  simp [box, Fintype.mem_piFinset]

theorem mem_shiftedBox_iff (n B : Nat) (δ : Fin n → Int) (x : Fin n → Int) :
    x ∈ shiftedBox n B δ ↔ ∀ i, x i ∈ shiftedInterval B (δ i) := by
  simp [shiftedBox, Fintype.mem_piFinset]

/-- Cardinality of the centered interval `[-B, B]` is `2B+1`. -/
theorem interval_card (B : Nat) : (interval B).card = 2 * B + 1 := by
  classical
  have hB : (0 : Int) ≤ (B : Int) := by
    exact_mod_cast (Nat.zero_le B)
  have hnonneg : (0 : Int) ≤ (B : Int) + 1 + (B : Int) := by
    have h1 : (0 : Int) ≤ (1 : Int) := by decide
    have hB1 : (0 : Int) ≤ (B : Int) + 1 := add_nonneg hB h1
    simpa [add_assoc] using add_nonneg hB1 hB

  have htoNat : ((B : Int) + 1 + (B : Int)).toNat = 2 * B + 1 := by
    apply Int.ofNat.inj
    calc
      ((B : Int) + 1 + (B : Int)).toNat
          = ((B : Int) + 1 + (B : Int)) := by
              exact Int.toNat_of_nonneg hnonneg
      _ = ((2 * B + 1 : Nat) : Int) := by
            have hNat : (B + B + 1 : Nat) = 2 * B + 1 := by
              simp [two_mul]
            calc
              (B : Int) + 1 + (B : Int) = (B : Int) + (B : Int) + 1 := by
                ac_rfl
              _ = ((B + B + 1 : Nat) : Int) := by
                    simp [add_assoc]
              _ = ((2 * B + 1 : Nat) : Int) := by
                    simp [hNat]

  -- `Int.card_Icc` gives a `toNat` expression which reduces to `htoNat`.
  simpa [interval, Int.card_Icc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htoNat

/-- Cardinality of the shifted interval `[-B+δ, B+δ]` is `2B+1`. -/
theorem shiftedInterval_card (B : Nat) (δ : Int) : (shiftedInterval B δ).card = 2 * B + 1 := by
  classical
  have hin :
      ((B : Int) + δ + 1 - (-(B : Int) + δ)) = ((B : Int) + 1 - (-(B : Int))) := by
    abel
  have : (shiftedInterval B δ).card = (interval B).card := by
    simp [shiftedInterval, interval, Int.card_Icc, hin]
  simpa [interval_card] using this

/-- Cardinality of the centered box `[-B, B]^n` is `(2B+1)^n`. -/
theorem box_card (n B : Nat) : (box n B).card = (2 * B + 1) ^ n := by
  classical
  simp [box, interval_card]

/-- Cardinality of the shifted box is `(2B+1)^n`. -/
theorem shiftedBox_card (n B : Nat) (δ : Fin n → Int) :
    (shiftedBox n B δ).card = (2 * B + 1) ^ n := by
  classical
  simp [shiftedBox, shiftedInterval_card]

/-- `x ∈ [-B+δ, B+δ]` iff `x-δ ∈ [-B, B]`. -/
theorem mem_shiftedInterval_iff_sub_mem_interval (B : Nat) (δ x : Int) :
    x ∈ shiftedInterval B δ ↔ x - δ ∈ interval B := by
  constructor
  · intro hx
    have hxI : (-(B : Int) + δ) ≤ x ∧ x ≤ ((B : Int) + δ) := by
      simpa [shiftedInterval, Finset.mem_Icc] using hx
    have : (-(B : Int)) ≤ x - δ ∧ x - δ ≤ (B : Int) := by
      constructor <;> linarith
    simpa [interval, Finset.mem_Icc] using this
  · intro hx
    have hxI : (-(B : Int)) ≤ x - δ ∧ x - δ ≤ (B : Int) := by
      simpa [interval, Finset.mem_Icc] using hx
    have : (-(B : Int) + δ) ≤ x ∧ x ≤ ((B : Int) + δ) := by
      constructor <;> linarith
    simpa [shiftedInterval, Finset.mem_Icc] using this

/-- 1D bound: `[-B,B] \ [-B+δ, B+δ]` has at most `|δ|` points. -/
theorem card_interval_sdiff_shiftedInterval_le (B : Nat) (δ : Int) :
    ((interval B \ shiftedInterval B δ).card) ≤ Int.natAbs δ := by
  simpa [interval, shiftedInterval, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using
    IntervalShift.card_Icc_sdiff_Icc_add_right_le_natAbs (a := (-(B : Int))) (b := (B : Int)) δ

/-- 1D bound in the opposite direction: `[-B+δ,B+δ] \ [-B,B]` has at most `|δ|` points. -/
theorem card_shiftedInterval_sdiff_interval_le (B : Nat) (δ : Int) :
    ((shiftedInterval B δ \ interval B).card) ≤ Int.natAbs δ := by
  -- Apply the 1D bound with shift `-δ`.
  simpa [interval, shiftedInterval, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using
    IntervalShift.card_Icc_sdiff_Icc_add_right_le_natAbs
      (a := (-(B : Int) + δ)) (b := ((B : Int) + δ)) (-δ)

/-- `x ∈ shiftedBox` iff `x - δ ∈ box`. -/
theorem mem_shiftedBox_iff_sub_mem_box (n B : Nat) (δ : Fin n → Int) (x : Fin n → Int) :
    x ∈ shiftedBox n B δ ↔ (fun i => x i - δ i) ∈ box n B := by
  constructor
  · intro hx
    apply (mem_box_iff (n := n) (B := B) (x := fun i => x i - δ i)).2
    intro i
    have hx' : x i ∈ shiftedInterval B (δ i) :=
      (mem_shiftedBox_iff (n := n) (B := B) (δ := δ) (x := x)).1 hx i
    exact (mem_shiftedInterval_iff_sub_mem_interval (B := B) (δ := δ i) (x := x i)).1 hx'
  · intro hx
    apply (mem_shiftedBox_iff (n := n) (B := B) (δ := δ) (x := x)).2
    intro i
    have hx' : x i - δ i ∈ interval B :=
      (mem_box_iff (n := n) (B := B) (x := fun i => x i - δ i)).1 hx i
    exact (mem_shiftedInterval_iff_sub_mem_interval (B := B) (δ := δ i) (x := x i)).2 hx'

/-- Bound: `box \ shiftedBox` has at most `∑ |δ i|` “slices” of size `|interval|^(n-1)`. -/
theorem card_box_sdiff_shiftedBox_le (n B : Nat) (δ : Fin n → Int) :
    (box n B \ shiftedBox n B δ).card ≤
      (Finset.univ.sum fun i : Fin n => Int.natAbs (δ i)) * (interval B).card ^ (n - 1) := by
  classical
  let bad : Fin n → Finset (Fin n → Int) :=
    fun i => (box n B).filter fun f => f i ∉ shiftedInterval B (δ i)

  have hsubset : box n B \ shiftedBox n B δ ⊆ Finset.univ.biUnion bad := by
    intro f hf
    rcases Finset.mem_sdiff.1 hf with ⟨hfbox, hfnot⟩
    have hnotall : ¬ ∀ i, f i ∈ shiftedInterval B (δ i) := by
      intro hall
      apply hfnot
      exact (mem_shiftedBox_iff (n := n) (B := B) (δ := δ) (x := f)).2 hall
    obtain ⟨i, hi⟩ := not_forall.1 hnotall
    refine Finset.mem_biUnion.2 ?_
    refine ⟨i, Finset.mem_univ i, ?_⟩
    simp [bad, hfbox, hi]

  have hcard_le_union : (box n B \ shiftedBox n B δ).card ≤ (Finset.univ.biUnion bad).card :=
    Finset.card_le_card hsubset

  have hunion : (Finset.univ.biUnion bad).card ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), (bad i).card :=
    Finset.card_biUnion_le

  have hcard_le_sum : (box n B \ shiftedBox n B δ).card ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), (bad i).card :=
    le_trans hcard_le_union hunion

  have hbad : ∀ i : Fin n, (bad i).card ≤ Int.natAbs (δ i) * (interval B).card ^ (n - 1) := by
    intro i
    let t : Finset Int := interval B \ shiftedInterval B (δ i)

    have hfilter : bad i = (box n B).filter (fun f => f i ∈ t) := by
      ext f
      constructor
      · intro hf
        have hfbox : f ∈ box n B := (Finset.mem_filter.1 hf).1
        have hnot : f i ∉ shiftedInterval B (δ i) := (Finset.mem_filter.1 hf).2
        have hi : f i ∈ interval B :=
          (mem_box_iff (n := n) (B := B) (x := f)).1 hfbox i
        have : f i ∈ t := by
          simp [t, Finset.mem_sdiff, hi, hnot]
        exact Finset.mem_filter.2 ⟨hfbox, this⟩
      · intro hf
        have hfbox : f ∈ box n B := (Finset.mem_filter.1 hf).1
        have hmem : f i ∈ t := (Finset.mem_filter.1 hf).2
        have hnot : f i ∉ shiftedInterval B (δ i) := by
          have : f i ∈ interval B \ shiftedInterval B (δ i) := by
            simpa [t] using hmem
          exact (Finset.mem_sdiff.1 this).2
        exact Finset.mem_filter.2 ⟨hfbox, hnot⟩

    have hcard_bad : (bad i).card = t.card * (interval B).card ^ (n - 1) := by
      calc
        (bad i).card = ((box n B).filter (fun f => f i ∈ t)).card := by
          simp [hfilter]
        _ = ∑ j ∈ t, #{f ∈ box n B | f i = j} := by
          simpa using
            (Finset.sum_card_fiberwise_eq_card_filter (s := box n B) (t := t) (g := fun f => f i)).symm
        _ = ∑ j ∈ t, (interval B).card ^ (n - 1) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hj' : j ∈ interval B := (Finset.mem_sdiff.1 (by simpa [t] using hj)).1
          simpa [box] using
            (Fintype.card_filter_piFinset_const_eq_of_mem (ι := Fin n) (κ := Int) (s := interval B)
              (i := i) (x := j) hj')
        _ = t.card * (interval B).card ^ (n - 1) := by
          simp

    have ht : t.card ≤ Int.natAbs (δ i) := by
      simpa [t] using card_interval_sdiff_shiftedInterval_le B (δ i)

    calc
      (bad i).card = t.card * (interval B).card ^ (n - 1) := hcard_bad
      _ ≤ Int.natAbs (δ i) * (interval B).card ^ (n - 1) :=
        Nat.mul_le_mul_right _ ht

  calc
    (box n B \ shiftedBox n B δ).card ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), (bad i).card :=
      hcard_le_sum
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), Int.natAbs (δ i) * (interval B).card ^ (n - 1) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hbad i
    _ = (Finset.univ.sum fun i : Fin n => Int.natAbs (δ i)) * (interval B).card ^ (n - 1) := by
      simpa using
        (Finset.sum_mul (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => Int.natAbs (δ i)) (a := (interval B).card ^ (n - 1))).symm

/-- Bound: `shiftedBox \ box` has at most `∑ |δ i|` “slices” of size `|interval|^(n-1)`. -/
theorem card_shiftedBox_sdiff_box_le (n B : Nat) (δ : Fin n → Int) :
    (shiftedBox n B δ \ box n B).card ≤
      (Finset.univ.sum fun i : Fin n => Int.natAbs (δ i)) * (interval B).card ^ (n - 1) := by
  classical
  let bad : Fin n → Finset (Fin n → Int) :=
    fun i => (shiftedBox n B δ).filter fun f => f i ∉ interval B

  have hsubset : shiftedBox n B δ \ box n B ⊆ Finset.univ.biUnion bad := by
    intro f hf
    rcases Finset.mem_sdiff.1 hf with ⟨hfshift, hfnot⟩
    have hnotall : ¬ ∀ i, f i ∈ interval B := by
      intro hall
      apply hfnot
      exact (mem_box_iff (n := n) (B := B) (x := f)).2 hall
    obtain ⟨i, hi⟩ := not_forall.1 hnotall
    refine Finset.mem_biUnion.2 ?_
    refine ⟨i, Finset.mem_univ i, ?_⟩
    simp [bad, hfshift, hi]

  have hcard_le_union : (shiftedBox n B δ \ box n B).card ≤ (Finset.univ.biUnion bad).card :=
    Finset.card_le_card hsubset

  have hunion : (Finset.univ.biUnion bad).card ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), (bad i).card :=
    Finset.card_biUnion_le

  have hcard_le_sum : (shiftedBox n B δ \ box n B).card ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), (bad i).card :=
    le_trans hcard_le_union hunion

  have hbad : ∀ i : Fin n, (bad i).card ≤ Int.natAbs (δ i) * (interval B).card ^ (n - 1) := by
    intro i
    let t : Finset Int := shiftedInterval B (δ i) \ interval B

    have hfilter : bad i = (shiftedBox n B δ).filter (fun f => f i ∈ t) := by
      ext f
      constructor
      · intro hf
        have hfshift : f ∈ shiftedBox n B δ := (Finset.mem_filter.1 hf).1
        have hnot : f i ∉ interval B := (Finset.mem_filter.1 hf).2
        have hi : f i ∈ shiftedInterval B (δ i) :=
          (mem_shiftedBox_iff (n := n) (B := B) (δ := δ) (x := f)).1 hfshift i
        have : f i ∈ t := by
          simp [t, Finset.mem_sdiff, hi, hnot]
        exact Finset.mem_filter.2 ⟨hfshift, this⟩
      · intro hf
        have hfshift : f ∈ shiftedBox n B δ := (Finset.mem_filter.1 hf).1
        have hmem : f i ∈ t := (Finset.mem_filter.1 hf).2
        have hnot : f i ∉ interval B := by
          have : f i ∈ shiftedInterval B (δ i) \ interval B := by
            simpa [t] using hmem
          exact (Finset.mem_sdiff.1 this).2
        exact Finset.mem_filter.2 ⟨hfshift, hnot⟩

    have hcard_bad : (bad i).card = t.card * (interval B).card ^ (n - 1) := by
      calc
        (bad i).card = ((shiftedBox n B δ).filter (fun f => f i ∈ t)).card := by
          simp [hfilter]
        _ = ∑ j ∈ t, #{f ∈ shiftedBox n B δ | f i = j} := by
          simpa using
            (Finset.sum_card_fiberwise_eq_card_filter (s := shiftedBox n B δ) (t := t)
              (g := fun f => f i)).symm
        _ = ∑ j ∈ t, (interval B).card ^ (n - 1) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hj' : j ∈ shiftedInterval B (δ i) := (Finset.mem_sdiff.1 (by simpa [t] using hj)).1
          -- Count functions in `shiftedBox` with the `i`th coordinate fixed to `j`.
          have : #{f ∈ shiftedBox n B δ | f i = j} =
              ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (shiftedInterval B (δ k)).card := by
            simpa [shiftedBox] using
              (Fintype.card_filter_piFinset_eq_of_mem (s := fun k : Fin n => shiftedInterval B (δ k)) (i := i)
                (a := j) hj')
          -- Each factor has cardinality `2B+1`.
          simp [this, shiftedInterval_card, interval_card]
        _ = t.card * (interval B).card ^ (n - 1) := by
          simp

    have ht : t.card ≤ Int.natAbs (δ i) := by
      simpa [t] using card_shiftedInterval_sdiff_interval_le B (δ i)

    calc
      (bad i).card = t.card * (interval B).card ^ (n - 1) := hcard_bad
      _ ≤ Int.natAbs (δ i) * (interval B).card ^ (n - 1) :=
        Nat.mul_le_mul_right _ ht

  calc
    (shiftedBox n B δ \ box n B).card ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), (bad i).card :=
      hcard_le_sum
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), Int.natAbs (δ i) * (interval B).card ^ (n - 1) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hbad i
    _ = (Finset.univ.sum fun i : Fin n => Int.natAbs (δ i)) * (interval B).card ^ (n - 1) := by
      simpa using
        (Finset.sum_mul (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => Int.natAbs (δ i)) (a := (interval B).card ^ (n - 1))).symm

/-- A generic counting lemma: uniforms on same-sized supports are statistically close,
with error bounded by the relative size of each support difference. -/
theorem statClose_uniformFinset_of_sdiff_card_le
    {α : Type} [DecidableEq α]
    (s t : Finset α) (hs : s.Nonempty) (ht : t.Nonempty)
    (hcard : s.card = t.card)
    (k : Nat)
    (hst : (s \ t).card ≤ k)
    (hts : (t \ s).card ≤ k) :
    StatClose (Dist.uniformFinset s hs) (Dist.uniformFinset t ht)
      ((k : ENNReal) / (s.card : ENNReal)) := by
  intro U
  classical

  have hs0 : (s.card : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hs.card_pos)

  -- Probability as intersection-card / |support|.
  let As : Finset α := s.filter fun a => a ∈ U
  let At : Finset α := t.filter fun a => a ∈ U

  have hPs : Dist.prob (Dist.uniformFinset s hs) U = (As.card : ENNReal) / (s.card : ENNReal) := by
    simp [As, Dist.prob_uniformFinset]

  have hPt : Dist.prob (Dist.uniformFinset t ht) U = (At.card : ENNReal) / (s.card : ENNReal) := by
    have : Dist.prob (Dist.uniformFinset t ht) U = (At.card : ENNReal) / (t.card : ENNReal) := by
      simp [At, Dist.prob_uniformFinset]
    simpa [hcard] using this

  -- Cardinality bounds on intersections.
  have hAs_le : As.card ≤ At.card + (s \ t).card := by
    have hsubset : As ⊆ At ∪ (s \ t) := by
      intro a ha
      have haS : a ∈ s := (Finset.mem_filter.1 ha).1
      have haU : a ∈ U := (Finset.mem_filter.1 ha).2
      by_cases hat : a ∈ t
      · have : a ∈ At := by
          simp [At, hat, haU]
        exact Finset.mem_union.2 (Or.inl this)
      · have : a ∈ (s \ t) := by
          simp [Finset.mem_sdiff, haS, hat]
        exact Finset.mem_union.2 (Or.inr this)
    calc
      As.card ≤ (At ∪ (s \ t)).card := Finset.card_le_card hsubset
      _ ≤ At.card + (s \ t).card := Finset.card_union_le _ _

  have hAt_le : At.card ≤ As.card + (t \ s).card := by
    have hsubset : At ⊆ As ∪ (t \ s) := by
      intro a ha
      have haT : a ∈ t := (Finset.mem_filter.1 ha).1
      have haU : a ∈ U := (Finset.mem_filter.1 ha).2
      by_cases has' : a ∈ s
      · have : a ∈ As := by
          simp [As, has', haU]
        exact Finset.mem_union.2 (Or.inl this)
      · have : a ∈ (t \ s) := by
          simp [Finset.mem_sdiff, haT, has']
        exact Finset.mem_union.2 (Or.inr this)
    calc
      At.card ≤ (As ∪ (t \ s)).card := Finset.card_le_card hsubset
      _ ≤ As.card + (t \ s).card := Finset.card_union_le _ _

  have hP_le : Dist.prob (Dist.uniformFinset s hs) U
      ≤ Dist.prob (Dist.uniformFinset t ht) U + (k : ENNReal) / (s.card : ENNReal) := by
    have hAs_le' : (As.card : ENNReal) ≤ (At.card : ENNReal) + ((s \ t).card : ENNReal) := by
      exact_mod_cast hAs_le
    have hst' : ((s \ t).card : ENNReal) ≤ (k : ENNReal) := by
      exact_mod_cast hst
    calc
      Dist.prob (Dist.uniformFinset s hs) U
          = (As.card : ENNReal) / (s.card : ENNReal) := hPs
      _ ≤ ((At.card : ENNReal) + ((s \ t).card : ENNReal)) / (s.card : ENNReal) := by
            gcongr
      _ = (At.card : ENNReal) / (s.card : ENNReal) + ((s \ t).card : ENNReal) / (s.card : ENNReal) := by
            simp [div_eq_mul_inv, add_mul]
      _ ≤ (At.card : ENNReal) / (s.card : ENNReal) + (k : ENNReal) / (s.card : ENNReal) := by
            gcongr
      _ = Dist.prob (Dist.uniformFinset t ht) U + (k : ENNReal) / (s.card : ENNReal) := by
            simp [hPt]

  have hQ_le : Dist.prob (Dist.uniformFinset t ht) U
      ≤ Dist.prob (Dist.uniformFinset s hs) U + (k : ENNReal) / (s.card : ENNReal) := by
    have hAt_le' : (At.card : ENNReal) ≤ (As.card : ENNReal) + ((t \ s).card : ENNReal) := by
      exact_mod_cast hAt_le
    have hts' : ((t \ s).card : ENNReal) ≤ (k : ENNReal) := by
      exact_mod_cast hts
    calc
      Dist.prob (Dist.uniformFinset t ht) U
          = (At.card : ENNReal) / (s.card : ENNReal) := hPt
      _ ≤ ((As.card : ENNReal) + ((t \ s).card : ENNReal)) / (s.card : ENNReal) := by
            gcongr
      _ = (As.card : ENNReal) / (s.card : ENNReal) + ((t \ s).card : ENNReal) / (s.card : ENNReal) := by
            simp [div_eq_mul_inv, add_mul]
      _ ≤ (As.card : ENNReal) / (s.card : ENNReal) + (k : ENNReal) / (s.card : ENNReal) := by
            gcongr
      _ = Dist.prob (Dist.uniformFinset s hs) U + (k : ENNReal) / (s.card : ENNReal) := by
            simp [hPs]

  -- Conclude via `absSubENNReal`.
  unfold absSubENNReal
  refine max_le ?_ ?_
  · have : Dist.prob (Dist.uniformFinset s hs) U
        ≤ (k : ENNReal) / (s.card : ENNReal) + Dist.prob (Dist.uniformFinset t ht) U := by
      simpa [add_comm, add_left_comm, add_assoc] using hP_le
    exact (tsub_le_iff_right.2 this)
  · have : Dist.prob (Dist.uniformFinset t ht) U
        ≤ (k : ENNReal) / (s.card : ENNReal) + Dist.prob (Dist.uniformFinset s hs) U := by
      simpa [add_comm, add_left_comm, add_assoc] using hQ_le
    exact (tsub_le_iff_right.2 this)

/-- Mapping `CenteredBounded.int` by `x ↦ x + δ` yields the uniform distribution on `shiftedInterval`. -/
theorem map_add_int_eq_uniformFinset_shiftedInterval (B : Nat) (δ : Int) :
    Dist.map (fun x : Int => x + δ) (int B) =
      Dist.uniformFinset (shiftedInterval B δ) (shiftedInterval_nonempty B δ) := by
  ext x  -- Evaluate the mapped PMF at `x`.
  have hmap : (Dist.map (fun y : Int => y + δ) (int B)).toPMF x = (int B).toPMF (x - δ) := by
    change (PMF.map (fun y : Int => y + δ) (int B).toPMF) x = (int B).toPMF (x - δ)
    rw [PMF.map_apply]

    have hdec :
        (∑' a : Int,
            @ite ENNReal (x = a + δ) (Classical.propDecidable (x = a + δ)) ((int B).toPMF a) 0) =
          ∑' a : Int, if x = a + δ then (int B).toPMF a else 0 := by
      refine tsum_congr fun a => ?_
      by_cases h : x = a + δ <;> simp [h]

    rw [hdec]

    calc
      (∑' a : Int, if x = a + δ then (int B).toPMF a else 0) =
          ∑' a : Int, if a = x - δ then (int B).toPMF (x - δ) else 0 := by
            refine tsum_congr fun a => ?_
            by_cases ha : x = a + δ
            · have ha' : a = x - δ := eq_sub_of_add_eq ha.symm
              calc
                (if x = a + δ then (int B).toPMF a else 0) = (int B).toPMF a := by
                  simp [ha]
                _ = (int B).toPMF (x - δ) := by
                  simp [ha']
                _ = (if a = x - δ then (int B).toPMF (x - δ) else 0) := by
                  simp [ha']
            · have ha' : a ≠ x - δ := by
                intro hax
                have : x = a + δ := by
                  simp [hax]
                exact ha this
              calc
                (if x = a + δ then (int B).toPMF a else 0) = 0 := by
                  simp [ha]
                _ = (if a = x - δ then (int B).toPMF (x - δ) else 0) := by
                  simp [ha']
      _ = (int B).toPMF (x - δ) := by simp

  -- Evaluate the base uniform PMF at `x-δ`.

  -- Evaluate the base uniform PMF at `x-δ`.
  have hbase : (int B).toPMF (x - δ) =
      if x - δ ∈ interval B then (1 : ENNReal) / (interval B).card else 0 := by
    simp [int, Dist.uniformFinset, PMF.uniformOfFinset_apply]

  -- Evaluate the shifted uniform PMF at `x`.
  have hshift : (Dist.uniformFinset (shiftedInterval B δ) (shiftedInterval_nonempty B δ)).toPMF x =
      if x ∈ shiftedInterval B δ then (1 : ENNReal) / (shiftedInterval B δ).card else 0 := by
    simp [Dist.uniformFinset, PMF.uniformOfFinset_apply]

  -- Relate membership and cardinalities.
  have hxmem : (x - δ ∈ interval B) ↔ (x ∈ shiftedInterval B δ) := by
    simp [mem_shiftedInterval_iff_sub_mem_interval]

  have hcard : (shiftedInterval B δ).card = (interval B).card := by
    simp [interval_card, shiftedInterval_card]

  -- Finish by cases on membership.
  by_cases hx : x ∈ shiftedInterval B δ
  · have hx' : x - δ ∈ interval B := (hxmem.2 hx)
    simp [hmap, hbase, hshift, hx, hx', hcard]
  · have hx' : x - δ ∉ interval B := by
      intro h
      exact hx (hxmem.1 h)
    simp [hmap, hbase, hshift, hx, hx']

/-- Mapping `CenteredBounded.vec` by coordinatewise `+ δ` yields the uniform distribution on `shiftedBox`. -/
theorem map_add_vec_eq_uniformFinset_shiftedBox (n B : Nat) (δ : Fin n → Int) :
    Dist.map (fun x : Fin n → Int => fun i => x i + δ i) (vec n B) =
      Dist.uniformFinset (shiftedBox n B δ) (shiftedBox_nonempty n B δ) := by
  classical
  let shift : (Fin n → Int) → (Fin n → Int) := fun y i => y i + δ i
  let unshift : (Fin n → Int) → (Fin n → Int) := fun x i => x i - δ i
  ext x

  change (Dist.map shift (vec n B)).toPMF x =
      (Dist.uniformFinset (shiftedBox n B δ) (shiftedBox_nonempty n B δ)).toPMF x

  have hmap : (Dist.map shift (vec n B)).toPMF x = (vec n B).toPMF (unshift x) := by
    change (PMF.map shift (vec n B).toPMF) x = (vec n B).toPMF (unshift x)
    rw [PMF.map_apply]

    have hdec :
        (∑' a : Fin n → Int,
            @ite ENNReal (x = shift a) (Classical.propDecidable (x = shift a)) ((vec n B).toPMF a) 0) =
          ∑' a : Fin n → Int, if x = shift a then (vec n B).toPMF a else 0 := by
      refine tsum_congr fun a => ?_
      by_cases h : x = shift a <;> simp [h]

    rw [hdec]

    calc
      (∑' a : Fin n → Int, if x = shift a then (vec n B).toPMF a else 0) =
          ∑' a : Fin n → Int, if a = unshift x then (vec n B).toPMF (unshift x) else 0 := by
            refine tsum_congr fun a => ?_
            by_cases ha : x = shift a
            · have ha' : a = unshift x := by
                funext i
                have hxi : x i = a i + δ i := by
                  simpa [shift] using congrArg (fun f : Fin n → Int => f i) ha
                have : a i = x i - δ i := eq_sub_of_add_eq hxi.symm
                simpa [unshift] using this
              calc
                (if x = shift a then (vec n B).toPMF a else 0) = (vec n B).toPMF a := by
                  simp [ha]
                _ = (vec n B).toPMF (unshift x) := by
                  simp [ha']
                _ = (if a = unshift x then (vec n B).toPMF (unshift x) else 0) := by
                  simp [ha']
            · have ha' : a ≠ unshift x := by
                intro hax
                have : x = shift a := by
                  funext i
                  have : a i = x i - δ i := by
                    simpa [unshift] using congrArg (fun f : Fin n → Int => f i) hax
                  -- Rearranged form of `sub_add_cancel`.
                  simp [shift, this]
                exact ha this
              calc
                (if x = shift a then (vec n B).toPMF a else 0) = 0 := by
                  simp [ha]
                _ = (if a = unshift x then (vec n B).toPMF (unshift x) else 0) := by
                  simp [ha']
      _ = (vec n B).toPMF (unshift x) := by simp

  have hbase : (vec n B).toPMF (unshift x) =
      if unshift x ∈ box n B then (1 : ENNReal) / (box n B).card else 0 := by
    simp [vec, box, unshift, Dist.uniformFinset, PMF.uniformOfFinset_apply]

  have hshift : (Dist.uniformFinset (shiftedBox n B δ) (shiftedBox_nonempty n B δ)).toPMF x =
      if x ∈ shiftedBox n B δ then (1 : ENNReal) / (shiftedBox n B δ).card else 0 := by
    simp [Dist.uniformFinset, PMF.uniformOfFinset_apply]

  have hxmem : (unshift x ∈ box n B) ↔ (x ∈ shiftedBox n B δ) := by
    simpa [unshift] using
      (mem_shiftedBox_iff_sub_mem_box (n := n) (B := B) (δ := δ) (x := x)).symm

  have hcard : (shiftedBox n B δ).card = (box n B).card := by
    simp [box_card, shiftedBox_card]

  by_cases hx : x ∈ shiftedBox n B δ
  · have hx' : unshift x ∈ box n B := (hxmem.2 hx)
    simp [hmap, hbase, hshift, hx, hx', hcard]
  · have hx' : unshift x ∉ box n B := by
      intro h
      exact hx (hxmem.1 h)
    simp [hmap, hbase, hshift, hx, hx']


/-- If `|δ| ≤ Bhide - Bacc`, then shifting `[-Bacc,Bacc]` by `δ` stays within `[-Bhide,Bhide]`. -/
theorem shiftedInterval_subset_interval_of_natAbs_le
    (Bacc Bhide : Nat) (δ : Int)
    (hB : Bacc ≤ Bhide)
    (hδ : Int.natAbs δ ≤ Bhide - Bacc) :
    shiftedInterval Bacc δ ⊆ interval Bhide := by
  intro x hx
  have hxI : (-(Bacc : Int) + δ) ≤ x ∧ x ≤ (Bacc : Int) + δ := by
    simpa [shiftedInterval, Finset.mem_Icc] using hx
  have habs : |δ| ≤ (Bhide - Bacc : Int) := by
    have : (δ.natAbs : Int) ≤ (Bhide - Bacc : Int) := by
      exact_mod_cast hδ
    simpa [Int.natCast_natAbs] using this
  have hNat : Bacc + (Bhide - Bacc) = Bhide := Nat.add_sub_of_le hB
  have hNatInt : (Bhide : Int) = (Bacc : Int) + (Bhide - Bacc : Int) := by
    exact_mod_cast hNat.symm
  have hx_upper : x ≤ (Bhide : Int) := by
    calc
      x ≤ (Bacc : Int) + δ := hxI.2
      _ ≤ (Bacc : Int) + |δ| := add_le_add_right (le_abs_self δ) (Bacc : Int)
      _ ≤ (Bacc : Int) + (Bhide - Bacc : Int) := add_le_add_right habs (Bacc : Int)
      _ = (Bhide : Int) := by
            exact_mod_cast hNat
  have hx_lower : (-(Bhide : Int)) ≤ x := by
    have hδlower : -(Bhide - Bacc : Int) ≤ δ := (abs_le.mp habs).1
    have hstep : (-(Bacc : Int)) - (Bhide - Bacc : Int) ≤ (-(Bacc : Int)) + δ :=
      add_le_add_right hδlower (-(Bacc : Int))
    have hrewrite : (-(Bhide : Int)) = (-(Bacc : Int)) - (Bhide - Bacc : Int) := by
      calc
        (-(Bhide : Int)) = -((Bacc : Int) + (Bhide - Bacc : Int)) :=
            congrArg (fun z : Int => -z) hNatInt
        _ = (-(Bacc : Int)) - (Bhide - Bacc : Int) := by
            simp [sub_eq_add_neg]
    have : (-(Bhide : Int)) ≤ (-(Bacc : Int)) + δ := by
      simpa [hrewrite] using hstep
    exact le_trans this hxI.1
  simpa [interval, Finset.mem_Icc] using And.intro hx_lower hx_upper

/-- If every coordinate shift is small, a shifted centered box stays within a larger centered box. -/
theorem shiftedBox_subset_box_of_natAbs_le
    (n Bacc Bhide : Nat) (δ : Fin n → Int)
    (hB : Bacc ≤ Bhide)
    (hδ : ∀ i : Fin n, Int.natAbs (δ i) ≤ Bhide - Bacc) :
    shiftedBox n Bacc δ ⊆ box n Bhide := by
  intro x hx
  apply (mem_box_iff (n := n) (B := Bhide) (x := x)).2
  intro i
  have hx' : x i ∈ shiftedInterval Bacc (δ i) :=
    (mem_shiftedBox_iff (n := n) (B := Bacc) (δ := δ) (x := x)).1 hx i
  exact shiftedInterval_subset_interval_of_natAbs_le (Bacc := Bacc) (Bhide := Bhide) (δ := δ i)
    hB (hδ i) hx'

/-- Acceptance probability for a shifted centered-bounded vector sampler, when the shift stays within a margin.

If `y` is uniform on `[-Bhide,Bhide]^n` and `|δ i| ≤ Bhide - Bacc` for all `i`, then
`y + δ ∈ [-Bacc,Bacc]^n` with probability `|box Bacc| / |box Bhide|`. -/
theorem prob_map_add_vec_mem_box_of_shift_le
    (n Bacc Bhide : Nat) (δ : Fin n → Int)
    (hB : Bacc ≤ Bhide)
    (hδ : ∀ i : Fin n, Int.natAbs (δ i) ≤ Bhide - Bacc) :
    Dist.prob
        (Dist.map (fun y : Fin n → Int => fun i => y i + δ i) (vec n Bhide))
        (box n Bacc : Set (Fin n → Int)) =
      ((box n Bacc).card : ENNReal) / ((box n Bhide).card : ENNReal) := by
  classical
  let shift : (Fin n → Int) → (Fin n → Int) := fun y i => y i + δ i
  have hpre :
      shift ⁻¹' (box n Bacc : Set (Fin n → Int)) =
        (shiftedBox n Bacc (fun i => -δ i) : Set (Fin n → Int)) := by
    ext y
    simpa [shift, Set.preimage, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (mem_shiftedBox_iff_sub_mem_box (n := n) (B := Bacc) (δ := fun i => -δ i) (x := y)).symm

  have hsub :
      shiftedBox n Bacc (fun i => -δ i) ⊆ box n Bhide := by
    refine shiftedBox_subset_box_of_natAbs_le (n := n) (Bacc := Bacc) (Bhide := Bhide)
      (δ := fun i => -δ i) hB ?_
    intro i
    simpa using (hδ i)

  have hprob :
      Dist.prob (vec n Bhide) (shiftedBox n Bacc (fun i => -δ i) : Set (Fin n → Int)) =
        ((shiftedBox n Bacc (fun i => -δ i)).card : ENNReal) / ((box n Bhide).card : ENNReal) := by
    have hsub' : shiftedBox n Bacc (fun i => -δ i) ⊆ Fintype.piFinset (fun _ : Fin n => interval Bhide) := by
      simpa [box] using hsub
    have hinter :
        (Fintype.piFinset (fun _ : Fin n => interval Bhide) ∩ shiftedBox n Bacc (fun i => -δ i)) =
          shiftedBox n Bacc (fun i => -δ i) :=
      Finset.inter_eq_right.2 hsub'
    simp [vec, box, Dist.prob_uniformFinset, Finset.filter_mem_eq_inter, hinter]

  have hcard : (shiftedBox n Bacc (fun i => -δ i)).card = (box n Bacc).card := by
    simp [shiftedBox_card, box_card]

  calc
    Dist.prob (Dist.map shift (vec n Bhide)) (box n Bacc : Set (Fin n → Int)) =
        Dist.prob (vec n Bhide) (shift ⁻¹' (box n Bacc : Set (Fin n → Int))) := by
          simpa using
            (Dist.prob_map_preimage (d := vec n Bhide) (f := shift)
              (s := (box n Bacc : Set (Fin n → Int))))
    _ = Dist.prob (vec n Bhide) (shiftedBox n Bacc (fun i => -δ i) : Set (Fin n → Int)) := by
          simp [hpre]
    _ = ((shiftedBox n Bacc (fun i => -δ i)).card : ENNReal) / ((box n Bhide).card : ENNReal) := hprob
    _ = ((box n Bacc).card : ENNReal) / ((box n Bhide).card : ENNReal) := by
          simp [hcard]

/-- Statistical closeness for 1D centered-bounded sampling under a shift.

Error: `|δ| / (2B+1)`.
-/
theorem statClose_int_shift (B : Nat) (δ : Int) :
    StatClose (int B) (Dist.map (fun x : Int => x + δ) (int B))
      ((Int.natAbs δ : ENNReal) / (2 * B + 1 : ENNReal)) := by
  classical
  let s : Finset Int := interval B
  let t : Finset Int := shiftedInterval B δ
  have hs : s.Nonempty := interval_nonempty B
  have ht : t.Nonempty := shiftedInterval_nonempty B δ
  have hcard : s.card = t.card := by
    simp [s, t, interval_card, shiftedInterval_card]
  have hsd : (s \ t).card ≤ Int.natAbs δ := by
    simpa [s, t] using card_interval_sdiff_shiftedInterval_le B δ
  have hts : (t \ s).card ≤ Int.natAbs δ := by
    simpa [s, t] using card_shiftedInterval_sdiff_interval_le B δ

  have hmap : Dist.map (fun x : Int => x + δ) (int B) = Dist.uniformFinset t ht := by
    simpa [t] using map_add_int_eq_uniformFinset_shiftedInterval (B := B) (δ := δ)

  have hclose :
      StatClose (Dist.uniformFinset s hs) (Dist.uniformFinset t ht)
        ((Int.natAbs δ : ENNReal) / (s.card : ENNReal)) :=
    statClose_uniformFinset_of_sdiff_card_le (s := s) (t := t) hs ht hcard
      (k := Int.natAbs δ) hsd hts

  have hclose' :
      StatClose (int B) (Dist.uniformFinset t ht) ((Int.natAbs δ : ENNReal) / (2 * B + 1 : ENNReal)) := by
    simpa [int, s, interval_card] using hclose

  simpa [hmap] using hclose'


/-- Statistical closeness for centered-bounded vector sampling under a coordinatewise shift.

Error: `(∑ i, |δ i|) / (2B+1)`.
-/
theorem statClose_vec_shift (n B : Nat) (δ : Fin n → Int) :
    StatClose (vec n B) (Dist.map (fun x : Fin n → Int => fun i => x i + δ i) (vec n B))
      (((Finset.univ.sum fun i : Fin n => Int.natAbs (δ i) : Nat) : ENNReal) / (2 * B + 1 : ENNReal)) := by
  classical
  let s : Finset (Fin n → Int) := box n B
  let t : Finset (Fin n → Int) := shiftedBox n B δ
  have hs : s.Nonempty := box_nonempty n B
  have ht : t.Nonempty := shiftedBox_nonempty n B δ
  have hcard : s.card = t.card := by
    simp [s, t, box_card, shiftedBox_card]
  let k : Nat := (Finset.univ.sum fun i : Fin n => Int.natAbs (δ i)) * (interval B).card ^ (n - 1)
  have hsd : (s \ t).card ≤ k := by
    simpa [s, t, k] using card_box_sdiff_shiftedBox_le (n := n) (B := B) (δ := δ)
  have hts : (t \ s).card ≤ k := by
    simpa [s, t, k] using card_shiftedBox_sdiff_box_le (n := n) (B := B) (δ := δ)

  have hclose :
      StatClose (Dist.uniformFinset s hs) (Dist.uniformFinset t ht)
        ((k : ENNReal) / (s.card : ENNReal)) :=
    statClose_uniformFinset_of_sdiff_card_le (s := s) (t := t) hs ht hcard (k := k) hsd hts

  have hmap :
      Dist.map (fun x : Fin n → Int => fun i => x i + δ i) (vec n B) = Dist.uniformFinset t ht := by
    simpa [t] using map_add_vec_eq_uniformFinset_shiftedBox (n := n) (B := B) (δ := δ)

  have hclose' :
      StatClose (vec n B) (Dist.map (fun x : Fin n → Int => fun i => x i + δ i) (vec n B))
        ((k : ENNReal) / (s.card : ENNReal)) := by
    simpa [vec, s, box, hmap.symm] using hclose

  have hε : ((k : ENNReal) / (s.card : ENNReal)) =
      ((Finset.univ.sum fun i : Fin n => Int.natAbs (δ i) : Nat) : ENNReal) / (2 * B + 1 : ENNReal) := by
    cases n with
    | zero =>
        simp [s, k, box_card, interval_card]
    | succ n =>
        let base : ENNReal := (2 * B + 1 : Nat)
        have hbase0 : base ≠ 0 := by
          dsimp [base]
          exact_mod_cast (Nat.succ_ne_zero (2 * B))
        have hc0 : base ^ n ≠ 0 := by
          exact pow_ne_zero n hbase0
        have hbaseTop : base ≠ ⊤ := by
          dsimp [base]
          exact ENNReal.natCast_ne_top (2 * B + 1)
        have hcTop : base ^ n ≠ ⊤ := by
          exact ENNReal.pow_ne_top hbaseTop
        let a : ENNReal :=
          Finset.univ.sum fun i : Fin (Nat.succ n) => (Int.natAbs (δ i) : ENNReal)
        calc
          ((k : ENNReal) / (s.card : ENNReal)) = base ^ n * a / (base ^ n * base) := by
            simp [s, k, a, base, box_card, interval_card, pow_succ, mul_comm]
          _ = a / base := by
            simpa [mul_assoc] using
              (ENNReal.mul_div_mul_left (a := a) (b := base) (c := base ^ n) hc0 hcTop)
          _ = ((Finset.univ.sum fun i : Fin (Nat.succ n) => Int.natAbs (δ i) : Nat) : ENNReal) / (2 * B + 1 : ENNReal) := by
            simp [a, base]
  simpa [hε] using hclose'

/-- Statistical closeness between two different coordinatewise shifts of the centered-bounded vector sampler.

This is a corollary of `statClose_vec_shift`: shifting by `δ₂` instead of `δ₁` is the same as
shifting by `δ₂ - δ₁` after applying the first shift.
-/
theorem statClose_vec_shift_two (n B : Nat) (δ₁ δ₂ : Fin n → Int) :
    StatClose
      (Dist.map (fun x : Fin n → Int => fun i => x i + δ₁ i) (vec n B))
      (Dist.map (fun x : Fin n → Int => fun i => x i + δ₂ i) (vec n B))
      (((Finset.univ.sum fun i : Fin n => Int.natAbs (δ₂ i - δ₁ i) : Nat) : ENNReal) /
        (2 * B + 1 : ENNReal)) := by
  classical
  let δ : Fin n → Int := fun i => δ₂ i - δ₁ i
  -- Base shift bound.
  have h :
      StatClose (vec n B)
        (Dist.map (fun x : Fin n → Int => fun i => x i + δ i) (vec n B))
        (((Finset.univ.sum fun i : Fin n => Int.natAbs (δ i) : Nat) : ENNReal) /
          (2 * B + 1 : ENNReal)) := by
    simpa [δ] using statClose_vec_shift (n := n) (B := B) δ
  -- Apply the first shift to both sides (data processing).
  have hmap :
      StatClose
        (Dist.map (fun x : Fin n → Int => fun i => x i + δ₁ i) (vec n B))
        (Dist.map (fun x : Fin n → Int => fun i => x i + δ₁ i)
          (Dist.map (fun x : Fin n → Int => fun i => x i + δ i) (vec n B)))
        (((Finset.univ.sum fun i : Fin n => Int.natAbs (δ i) : Nat) : ENNReal) /
          (2 * B + 1 : ENNReal)) :=
    StatClose.map (p := vec n B) (q := Dist.map (fun x : Fin n → Int => fun i => x i + δ i) (vec n B))
      (ε := (((Finset.univ.sum fun i : Fin n => Int.natAbs (δ i) : Nat) : ENNReal) / (2 * B + 1 : ENNReal)))
      h (fun x : Fin n → Int => fun i => x i + δ₁ i)
  -- Simplify the composed map into a single shift by `δ₂`.
  have hcomp :
      Dist.map (fun x : Fin n → Int => fun i => x i + δ₁ i)
          (Dist.map (fun x : Fin n → Int => fun i => x i + δ i) (vec n B))
        = Dist.map (fun x : Fin n → Int => fun i => x i + δ₂ i) (vec n B) := by
    cases vec n B with
    | mk p =>
      -- Reduce to a pointwise identity of the shift functions.
      simp [Dist.map, PMF.map_comp]
      congr
      funext a i
      simp [Function.comp, δ, add_assoc, sub_add_cancel]
  -- Conclude.
  simpa [hcomp, δ] using hmap

end CenteredBounded

end

end IceNine.Proofs.Probability
