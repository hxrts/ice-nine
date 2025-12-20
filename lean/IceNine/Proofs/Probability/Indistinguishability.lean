/-
# Probability Layer: Statistical Indistinguishability

We start with a statistical notion of indistinguishability between
security-parameter-indexed distribution families.

This is intentionally lightweight:

- `Negligible ε` uses mathlib's `Asymptotics.SuperpolynomialDecay` along `atTop`.
- `Indistinguishable D₁ D₂` means: there exists a negligible error function `ε`
  such that, for every security parameter `κ` and every event `S`,
  the probabilities under `D₁ κ` and `D₂ κ` differ by at most `ε κ`.

This is a standard “for all events” definition (equivalent to total variation
distance when the supremum exists).
-/

import IceNine.Proofs.Probability.Dist
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false

namespace IceNine.Proofs.Probability

open scoped BigOperators
open Filter Asymptotics

noncomputable section

universe u

/-- Cryptographic negligible functions (superpolynomial decay) in the security parameter `κ`. -/
def Negligible (ε : Nat → ENNReal) : Prop :=
  Asymptotics.SuperpolynomialDecay atTop (fun κ : Nat => (κ : ENNReal)) ε

namespace Negligible

theorem mul_const {ε : Nat → ENNReal} (h : Negligible ε) (c : ENNReal) (hc : c ≠ ⊤) :
    Negligible (fun κ => ε κ * c) := by
  intro n
  have h0 : Tendsto (fun κ : Nat => (κ : ENNReal) ^ n * ε κ) atTop (nhds 0) := by
    simpa [Negligible] using (h n)
  have hmul : Tendsto (fun κ : Nat => ((κ : ENNReal) ^ n * ε κ) * c) atTop (nhds (0 * c)) :=
    ENNReal.Tendsto.mul_const h0 (Or.inr hc)
  simpa [Negligible, mul_assoc, mul_left_comm, mul_comm] using hmul



theorem mul_pow {ε : Nat → ENNReal} (h : Negligible ε) (d : Nat) :
    Negligible (fun κ => ((κ : ENNReal) ^ d) * ε κ) := by
  -- This is just a shift in the exponent in the definition.
  unfold Negligible at h ⊢
  intro n
  -- Use `h (n + d)` and rewrite `κ^(n+d)` as `κ^n * κ^d`.
  have hnd := h (n + d)
  -- Rearrange products.
  simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hnd

theorem eventually_eq {ε ε' : Nat → ENNReal} (h : Negligible ε) (hEq : ε' =ᶠ[atTop] ε) :
    Negligible ε' := by
  -- Negligibility is stable under eventual equality.
  unfold Negligible at h ⊢
  intro n
  have ht := h n
  have hEq' :
      (fun κ : Nat => (κ : ENNReal) ^ n * ε κ) =ᶠ[atTop]
        fun κ : Nat => (κ : ENNReal) ^ n * ε' κ := by
    filter_upwards [hEq] with κ hκ
    simp [hκ.symm]
  exact ht.congr' hEq'

theorem add {ε₁ ε₂ : Nat → ENNReal} (h₁ : Negligible ε₁) (h₂ : Negligible ε₂) :
    Negligible (fun κ => ε₁ κ + ε₂ κ) := by
  unfold Negligible at h₁ h₂ ⊢
  intro n
  have h1 := h₁ n
  have h2 := h₂ n
  have hadd :
      Tendsto (fun κ : Nat => (κ : ENNReal) ^ n * ε₁ κ + (κ : ENNReal) ^ n * ε₂ κ) atTop
        (nhds (0 + 0)) := h1.add h2
  have hadd0 :
      Tendsto (fun κ : Nat => (κ : ENNReal) ^ n * ε₁ κ + (κ : ENNReal) ^ n * ε₂ κ) atTop
        (nhds 0) := by
    simpa using hadd
  refine (Filter.Tendsto.congr (f₁ := fun κ : Nat => (κ : ENNReal) ^ n * ε₁ κ + (κ : ENNReal) ^ n * ε₂ κ)
      (f₂ := fun κ : Nat => (κ : ENNReal) ^ n * (ε₁ κ + ε₂ κ)) ?_) hadd0
  intro κ
  simpa using (mul_add ((κ : ENNReal) ^ n) (ε₁ κ) (ε₂ κ)).symm

theorem mul_invpoly {ε α0 : Nat → ENNReal} (hε : Negligible ε)
    (hinvpoly : ∃ d : Nat, ∀ᶠ κ in atTop, (α0 κ)⁻¹ ≤ (κ : ENNReal) ^ d) :
    Negligible (fun κ => 2 * ε κ / α0 κ) := by
  rcases hinvpoly with ⟨d, hpoly⟩
  have hpow : Negligible (fun κ => ((κ : ENNReal) ^ d) * ε κ) :=
    mul_pow hε d
  unfold Negligible at hpow ⊢
  intro n
  have htend := hpow n
  have hle' :
      (fun κ : Nat => ((κ : ENNReal) ^ n) * (2 * ε κ / α0 κ))
        ≤ᶠ[atTop] fun κ : Nat => ((κ : ENNReal) ^ n) * (2 * (((κ : ENNReal) ^ d) * ε κ)) := by
    filter_upwards [hpoly] with κ hκ
    have hinv : (2 * ε κ / α0 κ) ≤ 2 * (((κ : ENNReal) ^ d) * ε κ) := by
      have : (ε κ) * (α0 κ)⁻¹ ≤ (ε κ) * ((κ : ENNReal) ^ d) :=
        mul_le_mul_right hκ (ε κ)
      calc
        2 * ε κ / α0 κ = 2 * (ε κ * (α0 κ)⁻¹) := by
          simp [div_eq_mul_inv, mul_assoc]
        _ ≤ 2 * (ε κ * ((κ : ENNReal) ^ d)) := by
          exact mul_le_mul_right this 2
        _ = 2 * (((κ : ENNReal) ^ d) * ε κ) := by
          simp [mul_assoc, mul_comm]
    exact mul_le_mul_right hinv ((κ : ENNReal) ^ n)

  have h0 : Tendsto (fun _ : Nat => (0 : ENNReal)) atTop (nhds 0) := tendsto_const_nhds
  have h2 : Tendsto (fun κ : Nat => ((κ : ENNReal) ^ n) * (2 * (((κ : ENNReal) ^ d) * ε κ))) atTop (nhds 0) := by
    have hc : (2 : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.natCast_ne_top 2
    have : Tendsto (fun κ : Nat => ((κ : ENNReal) ^ n) * (((κ : ENNReal) ^ d) * ε κ)) atTop (nhds 0) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using htend
    have hmul := ENNReal.Tendsto.mul_const this (Or.inr hc)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h0 h2 ?_ hle'
  exact Eventually.of_forall (fun _ => by simp)
end Negligible

/-- Absolute difference on `ℝ≥0∞`, expressed via truncated subtraction. -/
def absSubENNReal (a b : ENNReal) : ENNReal :=
  max (a - b) (b - a)

/-- Statistical closeness of two distributions at error `ε`. -/
def StatClose {α : Type u} (p q : Dist α) (ε : ENNReal) : Prop :=
  ∀ s : Set α, absSubENNReal (Dist.prob p s) (Dist.prob q s) ≤ ε

/-- Statistical indistinguishability of distribution families. -/
def Indistinguishable {α : Type u} (D₁ D₂ : DistFamily α) : Prop :=
  ∃ ε : Nat → ENNReal, Negligible ε ∧ ∀ κ, StatClose (D₁ κ) (D₂ κ) (ε κ)

/-- Computational indistinguishability placeholder.

Currently, this is aliased to statistical indistinguishability.

A future version should quantify over (PPT) distinguishers and bound the resulting
advantage by a negligible function. -/
def CompIndistinguishable {α : Type u} (D₁ D₂ : DistFamily α) : Prop :=
  Indistinguishable D₁ D₂

end

end IceNine.Proofs.Probability
