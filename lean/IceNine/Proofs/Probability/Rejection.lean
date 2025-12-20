/-
# Probability Layer: Local Rejection Sampling

This file defines the distributions induced by the pure local rejection
sampling operations in `Protocol/Sign/LocalRejection.lean`.

Key idea:

The output distribution of “repeat i.i.d. sampling until accept” is the
conditional distribution of a single sample given acceptance, assuming
acceptance has nonzero probability mass.

We model that conditional distribution using `PMF.filter`, wrapped as `Dist.filter`.
-/

import IceNine.Protocol.Sign.LocalRejection
import IceNine.Proofs.Probability.Dist

set_option autoImplicit false

namespace IceNine.Proofs.Probability

noncomputable section

open IceNine.Protocol
open IceNine.Protocol.ThresholdConfig
open IceNine.Protocol.NormBounded

/-- The local-rejection acceptance set for responses `z`. -/
def acceptSet (S : Scheme) [NormBounded S.Secret] (cfg : ThresholdConfig) : Set S.Secret :=
  { z | (NormOp.checkLocal cfg z).isOk = true }

/-- Candidate response distribution from a nonce-pair distribution. -/
def candidateResponseDist (S : Scheme)
    (nonceDist : DistFamily (S.Secret × S.Secret))
    (bindingFactor : S.Scalar)
    (challenge : S.Challenge)
    (sk : S.Secret) : DistFamily S.Secret :=
  fun κ =>
    Dist.map
      (fun (nonces : S.Secret × S.Secret) =>
        let (hidingNonce, bindingNonce) := nonces
        IceNine.Protocol.LocalRejection.RejectionOp.computeZ
          (S := S)
          sk challenge hidingNonce bindingNonce bindingFactor)
      (nonceDist κ)


/-- Candidate responses for two secrets differ by an additive shift.

For fixed public parameters and nonce distribution, changing `sk` only shifts
`computeZ` by the difference `challenge • sk₂ - challenge • sk₁`. -/
theorem candidateResponseDist_shift
    {S : Scheme}
    (nonceDist : DistFamily (S.Secret × S.Secret))
    (bindingFactor : S.Scalar)
    (challenge : S.Challenge)
    (sk₁ sk₂ : S.Secret) :
    candidateResponseDist S nonceDist bindingFactor challenge sk₂ =
      fun κ =>
        Dist.map (fun z : S.Secret => z + (challenge • sk₂ - challenge • sk₁))
          (candidateResponseDist S nonceDist bindingFactor challenge sk₁ κ) := by
  funext κ
  ext z
  -- Reduce to a pointwise identity inside the `tsum` defining `PMF.map`.
  simp [candidateResponseDist, Dist.map, PMF.map_comp, Function.comp,
    IceNine.Protocol.LocalRejection.RejectionOp.computeZ]
  refine tsum_congr fun a => ?_
  have hshift : a.1 + bindingFactor • a.2 + challenge • sk₂ =
      a.1 + bindingFactor • a.2 + challenge • sk₁ + (challenge • sk₂ - challenge • sk₁) := by
    simp
  by_cases hz : z = a.1 + bindingFactor • a.2 + challenge • sk₂
  · have hz2 : z = a.1 + bindingFactor • a.2 + challenge • sk₁ + (challenge • sk₂ - challenge • sk₁) :=
      hz.trans hshift
    simp [hz]
  · have hz2 : z ≠ a.1 + bindingFactor • a.2 + challenge • sk₁ + (challenge • sk₂ - challenge • sk₁) := by
      intro h
      apply hz
      exact h.trans hshift.symm
    simp [hz]
/-- Accepted response distribution: condition the candidate distribution on `acceptSet`. -/
def acceptedResponseDist (S : Scheme)
    [NormBounded S.Secret]
    (cfg : Nat → ThresholdConfig)
    (nonceDist : DistFamily (S.Secret × S.Secret))
    (bindingFactor : S.Scalar)
    (challenge : S.Challenge)
    (sk : S.Secret)
    (hAccept :
      ∀ κ,
        ∃ z ∈ acceptSet S (cfg κ),
          z ∈ (candidateResponseDist S nonceDist bindingFactor challenge sk κ).toPMF.support) :
    DistFamily S.Secret :=
  fun κ =>
    Dist.filter
      (candidateResponseDist S nonceDist bindingFactor challenge sk κ)
      (acceptSet S (cfg κ))
      (hAccept κ)

end

end IceNine.Proofs.Probability
