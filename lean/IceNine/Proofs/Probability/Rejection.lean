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
import IceNine.Proofs.Probability.Lemmas

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
/-- Accepted response distribution.

We interpret the unbounded rejection loop as conditioning the candidate distribution on `acceptSet`.
If acceptance has zero probability mass (so conditioning is undefined), we fall back to the
candidate distribution.

This makes the definition total, which is convenient when `publicOK κ` only holds eventually. -/
def acceptedResponseDist (S : Scheme)
    [NormBounded S.Secret]
    (cfg : Nat → ThresholdConfig)
    (nonceDist : DistFamily (S.Secret × S.Secret))
    (bindingFactor : S.Scalar)
    (challenge : S.Challenge)
    (sk : S.Secret) :
    DistFamily S.Secret :=
  fun κ =>
    let cand := candidateResponseDist S nonceDist bindingFactor challenge sk κ
    let A : Set S.Secret := acceptSet S (cfg κ)
    if h0 : Dist.prob cand A = 0 then
      cand
    else
      Dist.filter cand A
        (Dist.exists_mem_support_of_prob_ne_zero (d := cand) (A := A) h0)

namespace StatClose

universe u

variable {S : Scheme} [NormBounded S.Secret]

/-- Statistical closeness of accepted-response distributions from a closeness bound on the
candidate-response distributions, assuming a uniform lower bound on acceptance probability.

This is the pointwise (fixed `κ`) conditioning lemma specialized to `acceptedResponseDist`. -/
theorem acceptedResponseDist_of_prob_ge
    (cfg : Nat → ThresholdConfig)
    (nonceDist : DistFamily (S.Secret × S.Secret))
    (bindingFactor : S.Scalar)
    (challenge : S.Challenge)
    (sk₁ sk₂ : S.Secret) (κ : Nat)
    {ε α0 : ENNReal}
    (hclose : StatClose
      (candidateResponseDist S nonceDist bindingFactor challenge sk₁ κ)
      (candidateResponseDist S nonceDist bindingFactor challenge sk₂ κ) ε)
    (hα0 : α0 ≠ 0)
    (hprob₁ : α0 ≤
      Dist.prob (candidateResponseDist S nonceDist bindingFactor challenge sk₁ κ)
        (acceptSet S (cfg κ)))
    (hprob₂ : α0 ≤
      Dist.prob (candidateResponseDist S nonceDist bindingFactor challenge sk₂ κ)
        (acceptSet S (cfg κ))) :
    StatClose
      (acceptedResponseDist S cfg nonceDist bindingFactor challenge sk₁ κ)
      (acceptedResponseDist S cfg nonceDist bindingFactor challenge sk₂ κ)
      (2 * ε / α0) := by
  classical
  set p : Dist S.Secret := candidateResponseDist S nonceDist bindingFactor challenge sk₁ κ
  set q : Dist S.Secret := candidateResponseDist S nonceDist bindingFactor challenge sk₂ κ
  set A : Set S.Secret := acceptSet S (cfg κ)

  have hpos : 0 < α0 := by
    simpa [pos_iff_ne_zero] using hα0
  have hpA0 : Dist.prob p A ≠ 0 := by
    have : 0 < Dist.prob p A := lt_of_lt_of_le hpos (by simpa [p, A] using hprob₁)
    exact ne_of_gt this
  have hqA0 : Dist.prob q A ≠ 0 := by
    have : 0 < Dist.prob q A := lt_of_lt_of_le hpos (by simpa [q, A] using hprob₂)
    exact ne_of_gt this

  let hpA : ∃ z ∈ A, z ∈ p.toPMF.support :=
    Dist.exists_mem_support_of_prob_ne_zero (d := p) (A := A) (by simpa [p, A] using hpA0)
  let hqA : ∃ z ∈ A, z ∈ q.toPMF.support :=
    Dist.exists_mem_support_of_prob_ne_zero (d := q) (A := A) (by simpa [q, A] using hqA0)

  have hcond : StatClose (Dist.filter p A hpA) (Dist.filter q A hqA) (2 * ε / α0) := by
    exact StatClose.filter (h := by simpa [p, q] using hclose)
      (A := A) (hpA := hpA) (hqA := hqA)
      (hαp := by simpa [p, A] using hprob₁)
      (hαq := by simpa [q, A] using hprob₂)
      (hα0 := hα0)

  simpa [acceptedResponseDist, p, q, A, hpA0, hqA0] using hcond

end StatClose
end

end IceNine.Proofs.Probability
