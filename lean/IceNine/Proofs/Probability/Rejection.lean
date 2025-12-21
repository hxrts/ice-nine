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
import IceNine.Proofs.Probability.RepeatUntil

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


/-!
## Bridge: Protocol Loop vs Distribution Model

The implementation-level local rejection loop (`Protocol/Sign/LocalRejection`) is expressed as
`localRejectionLoopM`. When instantiated with the `Dist` monad, its output distribution matches
`Dist.repeatOption` on the candidate response distribution.
-/

namespace Bridge

open IceNine.Protocol.LocalRejection

/-- One-step attempt distribution for the candidate response distribution equals sampling nonces and
running `RejectionOp.tryOnce`. -/
theorem attemptOption_candidate_eq_map_tryOnce
    {S : Scheme} [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (sk_i : S.Secret)
    (challenge : S.Challenge)
    (bindingFactor : S.Scalar)
    (nonceDist : Dist (S.Secret × S.Secret)) :
    Dist.attemptOption
        (Dist.map
          (fun (nonces : S.Secret × S.Secret) =>
            let (hidingNonce, bindingNonce) := nonces
            RejectionOp.computeZ (S := S) sk_i challenge hidingNonce bindingNonce bindingFactor)
          nonceDist)
        (acceptSet S cfg)
      =
      Dist.map
        (fun (nonces : S.Secret × S.Secret) =>
          let (hidingNonce, bindingNonce) := nonces
          RejectionOp.tryOnce (S := S) cfg sk_i challenge hidingNonce bindingNonce bindingFactor)
        nonceDist
:= by
  classical
  ext o
  -- Reduce both sides to a single `PMF.map` over the nonce distribution.
  simp [Dist.attemptOption, Dist.map, PMF.map_comp, Function.comp, acceptSet,
    RejectionOp.tryOnce, RejectionOp.computeZ]
  refine tsum_congr (fun a => ?_)
  by_cases h :
      o =
        if (NormOp.checkLocal cfg (a.1 + bindingFactor • a.2 + challenge • sk_i)).isOk = true then
          some (a.1 + bindingFactor • a.2 + challenge • sk_i)
        else none
  · simp [h]
  · simp [h]

/-- Mapping `LocalSignResult.getZ` over the monadic loop instantiated with `Dist` yields
`Dist.repeatOption` on the candidate response distribution. -/
theorem localRejectionLoopM_go_getZ_eq_repeatOption
    {S : Scheme} [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (partyId : S.PartyId)
    (sk_i : S.Secret)
    (challenge : S.Challenge)
    (bindingFactor : S.Scalar)
    (maxAttempts : Nat)
    (nonceDist : Dist (S.Secret × S.Secret)) :
    ∀ (attempt remaining : Nat),
      Dist.map (fun r : LocalSignResult S => LocalSignResult.getZ r)
        (localRejectionLoopM.go
          (S := S) (m := Dist)
          (cfg := cfg) (partyId := partyId) (sk_i := sk_i)
          (challenge := challenge) (bindingFactor := bindingFactor)
          (maxAttempts := maxAttempts) (sampleNonce := nonceDist)
          attempt remaining)
        =
        Dist.repeatOption
          (Dist.map
            (fun (nonces : S.Secret × S.Secret) =>
              let (hidingNonce, bindingNonce) := nonces
              RejectionOp.computeZ (S := S) sk_i challenge hidingNonce bindingNonce bindingFactor)
            nonceDist)
          (acceptSet S cfg)
          remaining
  | attempt, 0 => by
      -- No remaining attempts: always fail, so `getZ` is always `none`.
      -- Unfold `go` and use `map_pure`.
      simp [localRejectionLoopM.go, Dist.repeatOption]
      change
        Dist.map (fun r : LocalSignResult S => LocalSignResult.getZ r)
            (Dist.pure (.failure (.maxAttemptsExceeded partyId maxAttempts cfg.localBound)))
          = Dist.pure none
      simp [Dist.map_pure, LocalSignResult.getZ]
  | attempt, remaining + 1 => by
      -- Induction hypothesis for the recursive call (attempt counter increments, but `getZ` ignores it).
      have ih := localRejectionLoopM_go_getZ_eq_repeatOption cfg partyId sk_i challenge bindingFactor
        maxAttempts nonceDist (attempt + 1) remaining

      set cand : Dist S.Secret :=
        Dist.map
          (fun (nonces : S.Secret × S.Secret) =>
            let (hidingNonce, bindingNonce) := nonces
            RejectionOp.computeZ (S := S) sk_i challenge hidingNonce bindingNonce bindingFactor)
          nonceDist

      let cont : Option S.Secret → Dist (Option S.Secret) := fun
        | some z => Dist.pure (some z)
        | none => Dist.repeatOption cand (acceptSet S cfg) remaining

      let tryOnceFn : (S.Secret × S.Secret) → Option S.Secret := fun nonces =>
        RejectionOp.tryOnce (S := S) cfg sk_i challenge nonces.1 nonces.2 bindingFactor

      -- Unfold one step of the loop, push `map` through `bind`, then rewrite to `repeatOption`.
      calc
        Dist.map (fun r : LocalSignResult S => LocalSignResult.getZ r)
            (localRejectionLoopM.go
              (S := S) (m := Dist)
              (cfg := cfg) (partyId := partyId) (sk_i := sk_i)
              (challenge := challenge) (bindingFactor := bindingFactor)
              (maxAttempts := maxAttempts) (sampleNonce := nonceDist)
              attempt (remaining + 1))
            =
            Dist.map (fun r : LocalSignResult S => LocalSignResult.getZ r)
              (Dist.bind nonceDist (fun (nonces : S.Secret × S.Secret) =>
                match RejectionOp.tryOnce (S := S) cfg sk_i challenge nonces.1 nonces.2 bindingFactor with
                | some z => Dist.pure (.success z nonces.1 nonces.2 (attempt + 1))
                | none =>
                    localRejectionLoopM.go
                      (S := S) (m := Dist)
                      (cfg := cfg) (partyId := partyId) (sk_i := sk_i)
                      (challenge := challenge) (bindingFactor := bindingFactor)
                      (maxAttempts := maxAttempts) (sampleNonce := nonceDist)
                      (attempt + 1) remaining)) := by
                simp [localRejectionLoopM.go]
                rfl
        _ =
            Dist.bind nonceDist (fun nonces =>
              Dist.map (fun r : LocalSignResult S => LocalSignResult.getZ r)
                (match RejectionOp.tryOnce (S := S) cfg sk_i challenge nonces.1 nonces.2 bindingFactor with
                 | some z => Dist.pure (.success z nonces.1 nonces.2 (attempt + 1))
                 | none =>
                     localRejectionLoopM.go
                       (S := S) (m := Dist)
                       (cfg := cfg) (partyId := partyId) (sk_i := sk_i)
                       (challenge := challenge) (bindingFactor := bindingFactor)
                       (maxAttempts := maxAttempts) (sampleNonce := nonceDist)
                       (attempt + 1) remaining)) := by
                simpa using
                  (Dist.map_bind (d := nonceDist)
                    (f := fun nonces : S.Secret × S.Secret =>
                      match RejectionOp.tryOnce (S := S) cfg sk_i challenge nonces.1 nonces.2 bindingFactor with
                      | some z => Dist.pure (.success z nonces.1 nonces.2 (attempt + 1))
                      | none =>
                          localRejectionLoopM.go
                            (S := S) (m := Dist)
                            (cfg := cfg) (partyId := partyId) (sk_i := sk_i)
                            (challenge := challenge) (bindingFactor := bindingFactor)
                            (maxAttempts := maxAttempts) (sampleNonce := nonceDist)
                            (attempt + 1) remaining)
                    (g := fun r : LocalSignResult S => LocalSignResult.getZ r)
                  )
        _ =
            Dist.bind nonceDist (fun nonces => cont (tryOnceFn nonces)) := by
              -- It suffices to show the continuations agree pointwise.
              refine congrArg (fun k => Dist.bind nonceDist k) ?_
              funext nonces
              cases h : tryOnceFn nonces with
              | none =>
                  -- Recursive case.
                  -- The loop calls itself with `attempt+1`; `getZ` ignores the attempt count.
                  simpa [cont, tryOnceFn, cand, h, LocalSignResult.getZ] using ih
              | some z =>
                  -- Success case: `getZ` of a success is `some z`.
                  simp [cont, tryOnceFn, cand, h, Dist.map_pure, LocalSignResult.getZ]
        _ =
            Dist.bind (Dist.map tryOnceFn nonceDist) cont := by
              simpa [Function.comp] using
                (Dist.bind_map (d := nonceDist) (f := tryOnceFn) (g := cont)).symm
        _ =
            Dist.bind (Dist.attemptOption cand (acceptSet S cfg)) cont := by
              have hAttempt := attemptOption_candidate_eq_map_tryOnce
                (S := S) (cfg := cfg) (sk_i := sk_i) (challenge := challenge)
                (bindingFactor := bindingFactor) (nonceDist := nonceDist)
              -- `attemptOption … = map tryOnceFn …`.
              simpa [tryOnceFn, cand] using congrArg (fun d => Dist.bind d cont) hAttempt.symm
        _ =
            Dist.repeatOption cand (acceptSet S cfg) (remaining + 1) := by
              -- Unfold `repeatOption` and show the continuations agree.
              simp [Dist.repeatOption]
              refine congrArg (fun k => Dist.bind (Dist.attemptOption cand (acceptSet S cfg)) k) ?_
              funext x
              cases x <;> simp [cont]
/-- Top-level: mapping `getZ` over `localRejectionLoopM` equals the bounded repeat-option model. -/
theorem localRejectionLoopM_getZ_eq_repeatOption
    {S : Scheme} [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (partyId : S.PartyId)
    (sk_i : S.Secret)
    (challenge : S.Challenge)
    (bindingFactor : S.Scalar)
    (maxAttempts : Nat)
    (nonceDist : Dist (S.Secret × S.Secret)) :
    Dist.map (fun r : LocalSignResult S => LocalSignResult.getZ r)
        (localRejectionLoopM
          (S := S) (m := Dist)
          (cfg := cfg) (partyId := partyId) (sk_i := sk_i)
          (challenge := challenge) (bindingFactor := bindingFactor)
          (maxAttempts := maxAttempts) nonceDist)
      =
      Dist.repeatOption
        (Dist.map
          (fun (nonces : S.Secret × S.Secret) =>
            let (hidingNonce, bindingNonce) := nonces
            RejectionOp.computeZ (S := S) sk_i challenge hidingNonce bindingNonce bindingFactor)
          nonceDist)
        (acceptSet S cfg)
        maxAttempts := by
  simpa [localRejectionLoopM] using
    localRejectionLoopM_go_getZ_eq_repeatOption
      (S := S) cfg partyId sk_i challenge bindingFactor maxAttempts nonceDist 0 maxAttempts

end Bridge

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
