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
import Mathlib.Analysis.SpecificLimits.Normed
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

/-- Exponential decay is negligible: if `r < 1` then `κ ↦ r^κ` is negligible. -/
theorem pow_const {r : ENNReal} (hr : r < 1) :
    Negligible (fun κ : Nat => r ^ κ) := by
  unfold Negligible
  intro n
  -- Reduce to a real limit using `toReal` (all values are finite when `r < 1`).
  have hrTop : r ≠ (⊤ : ENNReal) := ne_of_lt (lt_trans hr (by simp))
  have hf : ∀ κ : Nat, ((κ : ENNReal) ^ n * r ^ κ) ≠ (⊤ : ENNReal) := by
    intro κ
    have hκ : ((κ : ENNReal) ^ n) ≠ (⊤ : ENNReal) :=
      ENNReal.pow_ne_top (ENNReal.natCast_ne_top κ)
    have hrκ : (r ^ κ) ≠ (⊤ : ENNReal) := ENNReal.pow_ne_top hrTop
    exact ENNReal.mul_ne_top hκ hrκ

  have hrReal : r.toReal < (1 : ℝ) := by
    have h1Top : (1 : ENNReal) ≠ (⊤ : ENNReal) := by simp
    have : r.toReal < (1 : ENNReal).toReal := (ENNReal.toReal_lt_toReal hrTop h1Top).2 hr
    simpa using this

  have htoReal :
      Tendsto (fun κ : Nat => (((κ : ENNReal) ^ n * r ^ κ).toReal)) atTop (nhds 0) := by
    have hEq :
        (fun κ : Nat => (((κ : ENNReal) ^ n * r ^ κ).toReal)) =
          fun κ : Nat => (κ : ℝ) ^ n * (r.toReal) ^ κ := by
      funext κ
      simp [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    simpa [hEq] using
      (tendsto_pow_const_mul_const_pow_of_lt_one n (hr := ENNReal.toReal_nonneg) (h'r := hrReal))

  exact (ENNReal.tendsto_toReal_zero_iff (f := fun κ : Nat => ((κ : ENNReal) ^ n * r ^ κ)) (hf := hf)).1 htoReal

/-- Polynomially many trials make a geometric failure probability negligible.

For `0 < d`, the exponent `κ^d` dominates `κ`, so `r^(κ^d)` is bounded above by `r^κ`. -/
theorem pow_poly {r : ENNReal} (hr : r < 1) {d : Nat} (hd : 0 < d) :
    Negligible (fun κ : Nat => r ^ (κ ^ d)) := by
  -- Compare to the simpler negligible function `κ ↦ r^κ`.
  have hbase : Negligible (fun κ : Nat => r ^ κ) := pow_const (r := r) hr
  unfold Negligible at hbase ⊢
  intro n
  have htend : Tendsto (fun κ : Nat => ((κ : ENNReal) ^ n) * (r ^ κ)) atTop (nhds 0) := hbase n
  have hle : ∀ κ : Nat, ((κ : ENNReal) ^ n) * (r ^ (κ ^ d)) ≤ ((κ : ENNReal) ^ n) * (r ^ κ) := by
    intro κ
    have hrle1 : r ≤ (1 : ENNReal) := le_of_lt hr
    have hk : κ ≤ κ ^ d := Nat.le_pow (a := κ) (b := d) hd
    have hpow : r ^ (κ ^ d) ≤ r ^ κ := by
      simpa using (pow_le_pow_of_le_one (ha₀ := by simp) (ha₁ := hrle1) hk)
    exact mul_le_mul_right hpow ((κ : ENNReal) ^ n)
  -- Squeeze between 0 and the simpler tail.
  have h0 : Tendsto (fun _ : Nat => (0 : ENNReal)) atTop (nhds 0) := tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h0 htend ?_ ?_
  · exact Eventually.of_forall (fun κ => by simp)
  · exact Eventually.of_forall hle
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

/-- A (possibly inefficient) distinguisher for distributions over `α`.

This is a *placeholder* interface: later we can restrict to PPT distinguishers. -/
abbrev Distinguisher (α : Type u) : Type u :=
  α → Bool

/-- Computational indistinguishability placeholder.

For now this is a *statistical* notion phrased via distinguishers: every boolean
test has negligible distinguishing advantage.

A future version should restrict to (PPT) distinguishers to obtain true
computational indistinguishability. -/
def CompIndistinguishable {α : Type u} (D₁ D₂ : DistFamily α) : Prop :=
  ∃ ε : Nat → ENNReal, Negligible ε ∧
    ∀ κ, ∀ A : Distinguisher α,
      absSubENNReal (Dist.prob (D₁ κ) (A ⁻¹' {true})) (Dist.prob (D₂ κ) (A ⁻¹' {true})) ≤ ε κ

namespace Indistinguishable


variable {α : Type u}

/-- Statistical indistinguishability implies distinguisher-based indistinguishability. -/
theorem comp {D₁ D₂ : DistFamily α} (h : Indistinguishable D₁ D₂) : CompIndistinguishable D₁ D₂ := by
  rcases h with ⟨ε, hεneg, hεclose⟩
  refine ⟨ε, hεneg, ?_⟩
  intro κ A
  exact hεclose κ (A ⁻¹' {true})

end Indistinguishable

namespace CompIndistinguishable


variable {α : Type u}

/-- Distinguisher-based indistinguishability implies statistical indistinguishability.

This uses classical choice to turn an arbitrary event `s : Set α` into the boolean test
`x ↦ decide (x ∈ s)`. -/
theorem stat {D₁ D₂ : DistFamily α} (h : CompIndistinguishable D₁ D₂) : Indistinguishable D₁ D₂ := by
  classical
  rcases h with ⟨ε, hεneg, hεclose⟩
  refine ⟨ε, hεneg, ?_⟩
  intro κ s
  let A : Distinguisher α := fun x => decide (x ∈ s)
  have hpre : A ⁻¹' {true} = s := by
    ext x
    simp [A]
  simpa [hpre] using hεclose κ A

end CompIndistinguishable

end

end IceNine.Proofs.Probability
