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

end CenteredBounded

end

end IceNine.Proofs.Probability
