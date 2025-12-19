/-
# Probability Layer: Interval Shift Bounds

Dilithium-style arguments about centered-bounded sampling often reduce to a simple
combinatorial fact: shifting an integer interval by `δ` can change membership of
at most `|δ|` points.

This file records that bound as a lemma about `Finset.Icc` on `Int`.
-/

import Mathlib.Data.Int.Interval
import Mathlib.Tactic

set_option autoImplicit false

namespace IceNine.Proofs.Probability

noncomputable section

open Finset

namespace IntervalShift

/-- Shifting an integer interval by `δ` can remove at most `|δ|` points from it. -/
theorem card_Icc_sdiff_Icc_add_right_le_natAbs (a b δ : Int) :
    ((Icc a b \ Icc (a + δ) (b + δ)).card) ≤ Int.natAbs δ := by
  classical
  by_cases hδ : 0 ≤ δ
  · -- Shift to the right: the only points lost are on the left boundary.
    have hsubset : Icc a b \ Icc (a + δ) (b + δ) ⊆ Icc a (a + δ - 1) := by
      intro x hx
      have hxIcc : x ∈ Icc a b := (mem_sdiff.1 hx).1
      have hxnot : x ∉ Icc (a + δ) (b + δ) := (mem_sdiff.1 hx).2
      have hax : a ≤ x ∧ x ≤ b := by simpa [mem_Icc] using hxIcc
      refine mem_Icc.2 ?_
      refine ⟨hax.1, ?_⟩
      -- If `x` were ≥ `a+δ`, then it would lie in the shifted interval since `x ≤ b ≤ b+δ`.
      have hxlt : x < a + δ := by
        have hxle_bd : x ≤ b + δ := by
          exact le_trans hax.2 (le_add_of_nonneg_right hδ)
        by_contra hge'
        have hge : a + δ ≤ x := le_of_not_gt hge'
        have : a + δ ≤ x ∧ x ≤ b + δ := ⟨hge, hxle_bd⟩
        exact hxnot (by simpa [mem_Icc] using this)
      omega

    have hcard :
        (Icc a b \ Icc (a + δ) (b + δ)).card ≤ (Icc a (a + δ - 1)).card :=
      card_le_card hsubset

    have hIcc : (Icc a (a + δ - 1)).card = δ.toNat := by
      simp

    have hNatAbs : δ.toNat = Int.natAbs δ := by
      apply Int.ofNat.inj
      -- Both sides cast back to `Int` are equal to `δ` under `0 ≤ δ`.
      calc
        (δ.toNat : Int) = δ := Int.toNat_of_nonneg hδ
        _ = (Int.natAbs δ : Int) := (Int.natAbs_of_nonneg hδ).symm

    exact hcard.trans (le_of_eq <| by simp [hIcc, hNatAbs])
  · -- Shift to the left: the only points lost are on the right boundary.
    have hδneg : δ ≤ 0 := le_of_not_ge hδ
    have hsubset : Icc a b \ Icc (a + δ) (b + δ) ⊆ Icc (b + δ + 1) b := by
      intro x hx
      have hxIcc : x ∈ Icc a b := (mem_sdiff.1 hx).1
      have hxnot : x ∉ Icc (a + δ) (b + δ) := (mem_sdiff.1 hx).2
      have hax : a ≤ x ∧ x ≤ b := by simpa [mem_Icc] using hxIcc
      refine mem_Icc.2 ?_
      refine ⟨?_, hax.2⟩
      -- If `x ≤ b+δ`, then `a+δ ≤ x` since `a+δ ≤ a ≤ x`, contradicting `hxnot`.
      have hxgt : b + δ < x := by
        have haδ : a + δ ≤ x := by
          have : a + δ ≤ a := by omega
          exact le_trans this hax.1
        by_contra hle'
        have hle : x ≤ b + δ := le_of_not_gt hle'
        have : a + δ ≤ x ∧ x ≤ b + δ := ⟨haδ, hle⟩
        exact hxnot (by simpa [mem_Icc] using this)
      omega

    have hcard :
        (Icc a b \ Icc (a + δ) (b + δ)).card ≤ (Icc (b + δ + 1) b).card :=
      card_le_card hsubset

    have hIcc : (Icc (b + δ + 1) b).card = (-δ).toNat := by
      simp

    have hNatAbs : (-δ).toNat = Int.natAbs δ := by
      apply Int.ofNat.inj
      have hneg : 0 ≤ -δ := by simpa using (neg_nonneg.mpr hδneg)
      -- Both sides cast back to `Int` are equal to `-δ` under `δ ≤ 0`.
      calc
        ((-δ).toNat : Int) = -δ := Int.toNat_of_nonneg hneg
        _ = (Int.natAbs δ : Int) := (Int.ofNat_natAbs_of_nonpos hδneg).symm

    exact hcard.trans (le_of_eq <| by simp [hIcc, hNatAbs])

end IntervalShift

end

end IceNine.Proofs.Probability
