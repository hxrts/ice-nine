/-
# Statistical Closeness for Lattice Candidate Responses

This file proves a first, distribution-level (statistical) indistinguishability fact for the
demo `latticeScheme` under a centered-bounded nonce model.

Key idea:

* Sample `y_hiding` uniformly from a centered box `[-B, B]^n`.
* Let the rest of the response computation be “public + fixed secret shift”.
* Changing the secret changes the candidate response by an additive shift.
* Shifting a centered-bounded uniform box changes at most a boundary fraction.

We keep the negligible/error-rate aspect explicit: the resulting bound is an *explicit* function
`candidateShiftError`, and any negligibility claim about it is a separate assumption about how
`B` scales with the security parameter.
-/

import IceNine.Proofs.Probability.CenteredBoundedShift
import IceNine.Proofs.Probability.Rejection
import IceNine.Proofs.Probability.Lattice

set_option autoImplicit false

namespace IceNine.Proofs.Probability

noncomputable section

open IceNine.Instances
open IceNine.Protocol

namespace Lattice

/-- Centered-bounded hiding nonce distribution family `y_hiding ∼ U([-B κ, B κ]^n)`. -/
def hidingNonceDist (p : LatticeParams) (B : Nat → Nat) : DistFamily (Fin p.n → Int) :=
  fun κ => CenteredBounded.vec p.n (B κ)

/-- Independent nonce-pair distribution that samples the *binding* nonce first (for proofs),
then the hiding nonce, and finally swaps into the expected `(y_hiding, y_binding)` order. -/
def nonceDistSwapProd (p : LatticeParams) (B : Nat → Nat)
    (bindingNonceDist : DistFamily (Fin p.n → Int)) :
    DistFamily ((Fin p.n → Int) × (Fin p.n → Int)) :=
  fun κ =>
    Dist.map Prod.swap (Dist.prod (bindingNonceDist κ) (hidingNonceDist p B κ))

/-- The explicit shift-distance bound produced by `CenteredBounded.statClose_vec_shift_two`
for secrets `sk₁, sk₂` and challenge `c` at security parameter `κ`. -/
def candidateShiftError (p : LatticeParams) (B : Nat → Nat) (c : Int)
    (sk₁ sk₂ : Fin p.n → Int) : Nat → ENNReal :=
  fun κ =>
    (((Finset.univ.sum fun i : Fin p.n => Int.natAbs ((c • sk₂ - c • sk₁) i) : Nat) : ENNReal) /
      (2 * B κ + 1 : ENNReal))

theorem candidateResponseDist_eq_bind
    (p : LatticeParams) (hb : HashBinding) (B : Nat → Nat)
    (bindingNonceDist : DistFamily (Fin p.n → Int))
    (bindingFactor : Int) (c : Int) (sk : Fin p.n → Int) (κ : Nat) :
    candidateResponseDist (S := latticeScheme (p := p) hb)
        (nonceDistSwapProd p B bindingNonceDist) bindingFactor c sk κ
      =
      Dist.bind (bindingNonceDist κ) (fun yb =>
        Dist.map
          (fun yh =>
            IceNine.Protocol.LocalRejection.RejectionOp.computeZ
              (S := latticeScheme (p := p) hb)
              sk c yh yb bindingFactor)
          (hidingNonceDist p B κ)) := by
  ext z
  -- Reduce to `PMF.map_bind` + `PMF.map_comp` on the underlying `PMF`.
  simp [candidateResponseDist, nonceDistSwapProd, hidingNonceDist, Dist.prod, Dist.bind, Dist.map,
    PMF.map_comp, PMF.map_bind, Function.comp, Prod.swap,
    IceNine.Protocol.LocalRejection.RejectionOp.computeZ, IceNine.Instances.latticeScheme]

/-- Pointwise statistical closeness for candidate responses under centered-bounded hiding nonces. -/
theorem statClose_candidateResponseDist_centeredBounded
    (p : LatticeParams) (hb : HashBinding) (B : Nat → Nat)
    (bindingNonceDist : DistFamily (Fin p.n → Int))
    (bindingFactor : Int) (c : Int) (sk₁ sk₂ : Fin p.n → Int) (κ : Nat) :
    StatClose
      (candidateResponseDist (S := latticeScheme (p := p) hb)
        (nonceDistSwapProd p B bindingNonceDist) bindingFactor c sk₁ κ)
      (candidateResponseDist (S := latticeScheme (p := p) hb)
        (nonceDistSwapProd p B bindingNonceDist) bindingFactor c sk₂ κ)
      (candidateShiftError p B c sk₁ sk₂ κ) := by
  -- Rewrite both candidate distributions as a `bind` over the binding nonce.
  have h₁ := candidateResponseDist_eq_bind (p := p) (hb := hb) (B := B)
    (bindingNonceDist := bindingNonceDist) (bindingFactor := bindingFactor) (c := c) (sk := sk₁)
    (κ := κ)
  have h₂ := candidateResponseDist_eq_bind (p := p) (hb := hb) (B := B)
    (bindingNonceDist := bindingNonceDist) (bindingFactor := bindingFactor) (c := c) (sk := sk₂)
    (κ := κ)
  -- Use the mixture lemma `StatClose.bind`, with per-branch closeness from `statClose_vec_shift_two`.
  -- The per-branch bound is independent of the binding nonce, since the `bindingFactor • yb` term cancels.
  simpa [h₁, h₂, candidateShiftError] using
    (StatClose.bind (p := bindingNonceDist κ) (f := fun yb =>
        Dist.map
          (fun yh =>
            IceNine.Protocol.LocalRejection.RejectionOp.computeZ
              (S := latticeScheme (p := p) hb)
              sk₁ c yh yb bindingFactor)
          (hidingNonceDist p B κ))
      (g := fun yb =>
        Dist.map
          (fun yh =>
            IceNine.Protocol.LocalRejection.RejectionOp.computeZ
              (S := latticeScheme (p := p) hb)
              sk₂ c yh yb bindingFactor)
          (hidingNonceDist p B κ))
      (ε := candidateShiftError p B c sk₁ sk₂ κ) (h := fun yb => by
        -- Apply the centered-bounded shift bound to the hiding nonce sampler.
        -- The two shifts differ by `c • sk₂ - c • sk₁` (the binding term cancels).
        have hshift :=
          CenteredBounded.statClose_vec_shift_two
            (n := p.n) (B := B κ)
            (δ₁ := bindingFactor • yb + c • sk₁)
            (δ₂ := bindingFactor • yb + c • sk₂)
        -- Simplify the shift functions and the bound.
        simpa [hidingNonceDist, IceNine.Protocol.LocalRejection.RejectionOp.computeZ, candidateShiftError,
          add_assoc] using hshift))

/-- Family-level indistinguishability for candidate responses, assuming the explicit error bound is negligible. -/
theorem indistinguishable_candidateResponseDist_centeredBounded
    (p : LatticeParams) (hb : HashBinding) (B : Nat → Nat)
    (bindingNonceDist : DistFamily (Fin p.n → Int))
    (bindingFactor : Int) (c : Int) (sk₁ sk₂ : Fin p.n → Int)
    (hNeg : Negligible (candidateShiftError p B c sk₁ sk₂)) :
    Indistinguishable
      (candidateResponseDist (S := latticeScheme (p := p) hb)
        (nonceDistSwapProd p B bindingNonceDist) bindingFactor c sk₁)
      (candidateResponseDist (S := latticeScheme (p := p) hb)
        (nonceDistSwapProd p B bindingNonceDist) bindingFactor c sk₂) := by
  refine ⟨candidateShiftError p B c sk₁ sk₂, hNeg, ?_⟩
  intro κ
  exact statClose_candidateResponseDist_centeredBounded (p := p) (hb := hb) (B := B)
    (bindingNonceDist := bindingNonceDist) (bindingFactor := bindingFactor) (c := c)
    (sk₁ := sk₁) (sk₂ := sk₂) (κ := κ)

end Lattice

end

end IceNine.Proofs.Probability
