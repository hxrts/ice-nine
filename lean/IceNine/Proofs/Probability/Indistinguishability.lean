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

end

end IceNine.Proofs.Probability
