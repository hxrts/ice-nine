/-
# Probability Layer: Centered Bounded Sampling

Dilithium-style lattice schemes sample secrets/nonces/openings from *centered bounded*
distributions (e.g. coefficients in `[-η, η]`).

This module provides simple concrete samplers as `Dist` values.

We model centered-bounded sampling as the uniform distribution on the integer interval
`[-B, B]`, and vectors as the uniform distribution on the product box `[-B, B]^n`.
-/

import IceNine.Proofs.Probability.Dist
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false

namespace IceNine.Proofs.Probability

noncomputable section

namespace CenteredBounded

/-- Map an index `i ∈ {0,…,2B}` to an integer in `[-B, B]`.

This is occasionally useful to connect the interval model back to an explicit finite sampler. -/
def finToCenteredInt (B : Nat) (i : Fin (2 * B + 1)) : Int :=
  (i.val : Int) - (B : Int)

/-- The centered interval finset `[-B, B]` as a `Finset Int`. -/
def interval (B : Nat) : Finset Int :=
  Finset.Icc (-(B : Int)) (B : Int)

theorem interval_nonempty (B : Nat) : (interval B).Nonempty := by
  have : (-(B : Int)) ≤ (B : Int) := by
    have h0 : (0 : Int) ≤ (B : Int) := by
      exact_mod_cast (Nat.zero_le B)
    exact neg_le_self h0
  dsimp [interval]
  exact Finset.nonempty_Icc.2 this

/-- Centered bounded distribution on `Int`, uniform on `[-B, B]`. -/
def int (B : Nat) : Dist Int :=
  Dist.uniformFinset (interval B) (interval_nonempty B)

/-- Centered bounded distribution on `Fin n → Int`, coefficientwise uniform on `[-B, B]`. -/
def vec (n B : Nat) : Dist (Fin n → Int) :=
  Dist.uniformFinset
    (Fintype.piFinset (fun _ : Fin n => interval B))
    ((interval_nonempty B).piFinset_const (ι := Fin n))

/-- κ-agnostic centered bounded coefficient family (useful for fixed-parameter schemes). -/
abbrev intFamily (B : Nat) : DistFamily Int :=
  fun _ => int B

/-- κ-agnostic centered bounded vector family (useful for fixed-parameter schemes). -/
abbrev vecFamily (n B : Nat) : DistFamily (Fin n → Int) :=
  fun _ => vec n B

end CenteredBounded

end

end IceNine.Proofs.Probability
