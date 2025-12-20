/-
# Acceptance Bounds for Lattice Candidate Responses

This file provides a concrete, combinatorial lower bound on the acceptance
probability for the demo `latticeScheme` under a centered-bounded nonce model.

We work with a simple acceptance event: membership in a centered box
`[-Bacc, Bacc]^n`, which is a subset of the protocol’s `acceptSet` (local norm
check). Under a margin condition, shifting a uniform box by a bounded amount
keeps that box inside the hiding-nonce support, yielding an exact acceptance
probability `|box Bacc| / |box Bh|`.

This is designed to let us *construct* a non-vacuous `ResponseIndependence`
instance for the lattice demo scheme with explicit bounds on secrets and public
parameters.
-/

import IceNine.Instances
import IceNine.Proofs.Core.Assumptions
import IceNine.Proofs.Probability.CenteredBoundedShift
import IceNine.Proofs.Probability.LatticeRejectionIndist
import IceNine.Proofs.Probability.Rejection
import IceNine.Proofs.Probability.Lemmas

set_option autoImplicit false

namespace IceNine.Proofs.Probability

noncomputable section

open IceNine.Instances
open IceNine.Protocol
open IceNine.Protocol.NormBounded
open IceNine.Protocol.ThresholdConfig

namespace Lattice

/-- A centered-box acceptance event for lattice responses: `z ∈ [-B, B]^n`. -/
def acceptBoxSet (p : LatticeParams) (B : Nat) : Set (Fin p.n → Int) :=
  (CenteredBounded.box p.n B : Set (Fin p.n → Int))

private theorem natAbs_le_of_mem_interval {B : Nat} {x : Int}
    (hx : x ∈ CenteredBounded.interval B) :
    Int.natAbs x ≤ B := by
  have hxI : (-(B : Int)) ≤ x ∧ x ≤ (B : Int) := by
    simpa [CenteredBounded.interval, Finset.mem_Icc] using hx
  have habs : |x| ≤ (B : Int) := (abs_le).2 hxI
  have hnat : (x.natAbs : Int) ≤ (B : Int) := by
    simpa [Int.natCast_natAbs] using habs
  exact (Int.ofNat_le.1 hnat)

private theorem natAbs_le_of_mem_box {n B : Nat} {x : Fin n → Int}
    (hx : x ∈ CenteredBounded.box n B) :
    ∀ i, Int.natAbs (x i) ≤ B := by
  intro i
  have hx' : ∀ j, x j ∈ CenteredBounded.interval B :=
    (CenteredBounded.mem_box_iff (n := n) (B := B) (x := x)).1 hx
  exact natAbs_le_of_mem_interval (hx' i)

/-- The centered-box event implies the protocol’s `acceptSet` for the lattice demo scheme. -/
theorem acceptBoxSet_subset_acceptSet
    (p : LatticeParams) (hb : HashBinding) (cfg : ThresholdConfig) :
    acceptBoxSet p cfg.localBound ⊆
      acceptSet (S := latticeScheme (p := p) hb) cfg := by
  classical
  intro z hz
  -- Use the `Instances` norm instance (ℓ∞ via `sup natAbs`).
  letI : NormBounded (Fin p.n → Int) := IceNine.Instances.intVecNormBounded

  have hzCoeff : ∀ i, Int.natAbs (z i) ≤ cfg.localBound := by
    exact natAbs_le_of_mem_box (n := p.n) (B := cfg.localBound) (x := z) hz

  have hnorm : NormBounded.norm z ≤ cfg.localBound := by
    -- With this local instance, `norm` is `intVecInfNorm`.
    change IceNine.Instances.intVecInfLeq cfg.localBound z
    exact IceNine.Instances.intVecInfLeq_of_coeff_bound (v := z) (B := cfg.localBound) hzCoeff

  -- Discharge the boolean check.
  unfold acceptSet
  change (NormOp.checkLocal cfg z).isOk = true
  simp [NormOp.checkLocal, NormOp.check, NormCheckResult.isOk, hnorm]



/-- Exact acceptance probability for the centered-box event, under a uniform margin condition.

The margin condition is stated using a *worst-case* bound `skBound` on secret coefficients.
-/
theorem prob_candidateResponseDist_acceptBoxSet_centeredBounded
    (p : LatticeParams) (hb : HashBinding)
    (cfg : ThresholdConfig)
    (Bh Bb skBound : Nat)
    (bindingFactor c : Int)
    (sk : Fin p.n → Int)
    (κ : Nat)
    (hB : cfg.localBound ≤ Bh)
    (hsk : ∀ i, Int.natAbs (sk i) ≤ skBound)
    (hshift : Int.natAbs bindingFactor * Bb + Int.natAbs c * skBound ≤ Bh - cfg.localBound) :
    Dist.prob
        (candidateResponseDist (S := latticeScheme (p := p) hb)
          (nonceDistSwapProd p (fun _ => Bh) (fun _ => CenteredBounded.vec p.n Bb))
          bindingFactor c sk κ)
        (acceptBoxSet p cfg.localBound)
      =
      ((CenteredBounded.box p.n cfg.localBound).card : ENNReal) /
        ((CenteredBounded.box p.n Bh).card : ENNReal) := by
  classical
  -- Expand the candidate distribution as a `bind` over the binding nonce.
  have hbind :=
    candidateResponseDist_eq_bind (p := p) (hb := hb) (B := fun _ => Bh)
      (bindingNonceDist := fun _ => CenteredBounded.vec p.n Bb)
      (bindingFactor := bindingFactor) (c := c) (sk := sk) (κ := κ)
  -- Abbreviations.
  let A : Set (Fin p.n → Int) := acceptBoxSet p cfg.localBound
  let α : ENNReal := ((CenteredBounded.box p.n cfg.localBound).card : ENNReal) /
    ((CenteredBounded.box p.n Bh).card : ENNReal)

  -- Start from the bind law.
  have hprob_bind :
      Dist.prob
          (candidateResponseDist (S := latticeScheme (p := p) hb)
            (nonceDistSwapProd p (fun _ => Bh) (fun _ => CenteredBounded.vec p.n Bb))
            bindingFactor c sk κ)
          A
        =
        ∑' yb,
          (CenteredBounded.vec p.n Bb).toPMF yb *
            Dist.prob
              (Dist.map
                (fun yh =>
                  IceNine.Protocol.LocalRejection.RejectionOp.computeZ
                    (S := latticeScheme (p := p) hb)
                    sk c yh yb bindingFactor)
                (CenteredBounded.vec p.n Bh))
              A := by
    -- Rewrite using `hbind` and unfold `Dist.prob_bind`.
    simp [hbind, hidingNonceDist, A, Dist.prob_bind]

  -- Show each term is `pmf yb * α` (outside support the pmf is 0).
  have hterm :
      ∀ yb,
        (CenteredBounded.vec p.n Bb).toPMF yb *
            Dist.prob
              (Dist.map
                (fun yh =>
                  IceNine.Protocol.LocalRejection.RejectionOp.computeZ
                    (S := latticeScheme (p := p) hb)
                    sk c yh yb bindingFactor)
                (CenteredBounded.vec p.n Bh))
              A
          = (CenteredBounded.vec p.n Bb).toPMF yb * α := by
    intro yb
    by_cases hyb : yb ∈ (CenteredBounded.vec p.n Bb).toPMF.support
    · -- Inside support: `yb ∈ box`, so the shift is bounded coordinatewise.
      have hybBox : yb ∈ CenteredBounded.box p.n Bb := by
        -- Support of the uniform-on-box sampler is exactly that box.
        simpa [CenteredBounded.vec, CenteredBounded.box, Dist.uniformFinset]
          using (PMF.mem_support_uniformOfFinset_iff (s := CenteredBounded.box p.n Bb)
            (hs := (CenteredBounded.box_nonempty p.n Bb)) yb) |>.1 hyb

      have hybCoeff : ∀ i, Int.natAbs (yb i) ≤ Bb :=
        natAbs_le_of_mem_box (n := p.n) (B := Bb) (x := yb) hybBox

      have hδ : ∀ i : Fin p.n,
          Int.natAbs ((bindingFactor • yb + c • sk) i) ≤ Bh - cfg.localBound := by
        intro i
        -- Bound the coordinatewise shift by triangle inequality and the global margin.
        have hadd :
            Int.natAbs ((bindingFactor * yb i) + (c * sk i)) ≤
              Int.natAbs (bindingFactor * yb i) + Int.natAbs (c * sk i) :=
          Int.natAbs_add_le _ _
        have hmul1 : Int.natAbs (bindingFactor * yb i) ≤ Int.natAbs bindingFactor * Bb := by
          calc
            Int.natAbs (bindingFactor * yb i)
                = Int.natAbs bindingFactor * Int.natAbs (yb i) := by
                    simp [Int.natAbs_mul]
            _ ≤ Int.natAbs bindingFactor * Bb := by
                    exact Nat.mul_le_mul_left _ (hybCoeff i)
        have hmul2 : Int.natAbs (c * sk i) ≤ Int.natAbs c * skBound := by
          calc
            Int.natAbs (c * sk i)
                = Int.natAbs c * Int.natAbs (sk i) := by
                    simp [Int.natAbs_mul]
            _ ≤ Int.natAbs c * skBound := by
                    exact Nat.mul_le_mul_left _ (hsk i)
        have : Int.natAbs ((bindingFactor * yb i) + (c * sk i)) ≤
            Int.natAbs bindingFactor * Bb + Int.natAbs c * skBound := by
          calc
            Int.natAbs ((bindingFactor * yb i) + (c * sk i))
                ≤ Int.natAbs (bindingFactor * yb i) + Int.natAbs (c * sk i) := hadd
            _ ≤ Int.natAbs bindingFactor * Bb + Int.natAbs c * skBound := by
                  exact Nat.add_le_add hmul1 hmul2
        -- Finish with the assumed margin.
        exact le_trans this hshift

      have hbranch :
          Dist.prob
              (Dist.map
                (fun yh : Fin p.n → Int =>
                  IceNine.Protocol.LocalRejection.RejectionOp.computeZ
                    (S := latticeScheme (p := p) hb)
                    sk c yh yb bindingFactor)
                (CenteredBounded.vec p.n Bh))
              A
            = α := by
        -- Rewrite `computeZ` into an explicit coordinatewise `+ δ` map.
        have :
            Dist.prob
                (Dist.map
                  (fun yh : Fin p.n → Int =>
                    fun i => yh i + (bindingFactor • yb + c • sk) i)
                  (CenteredBounded.vec p.n Bh))
                (CenteredBounded.box p.n cfg.localBound : Set (Fin p.n → Int))
              = ((CenteredBounded.box p.n cfg.localBound).card : ENNReal) /
                  ((CenteredBounded.box p.n Bh).card : ENNReal) :=
          CenteredBounded.prob_map_add_vec_mem_box_of_shift_le
            (n := p.n) (Bacc := cfg.localBound) (Bhide := Bh) (δ := bindingFactor • yb + c • sk)
            (hB := hB) (hδ := hδ)
        simpa [A, acceptBoxSet, α, IceNine.Protocol.LocalRejection.RejectionOp.computeZ, add_assoc]
          using this

      simpa using congrArg (fun t => (CenteredBounded.vec p.n Bb).toPMF yb * t) hbranch
    · -- Outside support: mass is 0.
      have hmass0 : (CenteredBounded.vec p.n Bb).toPMF yb = 0 := by
        simpa [PMF.support] using hyb
      simp [hmass0]

  -- Conclude by `tsum` congruence and `PMF.tsum_coe`.
  calc
    Dist.prob
        (candidateResponseDist (S := latticeScheme (p := p) hb)
          (nonceDistSwapProd p (fun _ => Bh) (fun _ => CenteredBounded.vec p.n Bb))
          bindingFactor c sk κ)
        A
        = ∑' yb,
            (CenteredBounded.vec p.n Bb).toPMF yb *
              Dist.prob
                (Dist.map
                  (fun yh =>
                    IceNine.Protocol.LocalRejection.RejectionOp.computeZ
                      (S := latticeScheme (p := p) hb)
                      sk c yh yb bindingFactor)
                  (CenteredBounded.vec p.n Bh))
                A := hprob_bind
    _ = ∑' yb, (CenteredBounded.vec p.n Bb).toPMF yb * α := by
          refine tsum_congr ?_
          intro yb
          simp [hterm yb]
    _ = α := by
          simp [ENNReal.tsum_mul_right, (CenteredBounded.vec p.n Bb).toPMF.tsum_coe]
    _ = ((CenteredBounded.box p.n cfg.localBound).card : ENNReal) /
          ((CenteredBounded.box p.n Bh).card : ENNReal) := rfl


/-- Lower bound on acceptance probability for the full `acceptSet`, via the centered-box event. -/
theorem prob_candidateResponseDist_acceptSet_ge_centeredBounded
    (p : LatticeParams) (hb : HashBinding)
    (cfg : ThresholdConfig)
    (Bh Bb skBound : Nat)
    (bindingFactor c : Int)
    (sk : Fin p.n → Int)
    (κ : Nat)
    (hB : cfg.localBound ≤ Bh)
    (hsk : ∀ i, Int.natAbs (sk i) ≤ skBound)
    (hshift : Int.natAbs bindingFactor * Bb + Int.natAbs c * skBound ≤ Bh - cfg.localBound) :
    ((CenteredBounded.box p.n cfg.localBound).card : ENNReal) /
        ((CenteredBounded.box p.n Bh).card : ENNReal)
      ≤
      Dist.prob
        (candidateResponseDist (S := latticeScheme (p := p) hb)
          (nonceDistSwapProd p (fun _ => Bh) (fun _ => CenteredBounded.vec p.n Bb))
          bindingFactor c sk κ)
        (acceptSet (S := latticeScheme (p := p) hb) cfg) := by
  let d : Dist (Fin p.n → Int) :=
    candidateResponseDist (S := latticeScheme (p := p) hb)
      (nonceDistSwapProd p (fun _ => Bh) (fun _ => CenteredBounded.vec p.n Bb))
      bindingFactor c sk κ

  have hbox :
      Dist.prob d (acceptBoxSet p cfg.localBound) =
        ((CenteredBounded.box p.n cfg.localBound).card : ENNReal) /
          ((CenteredBounded.box p.n Bh).card : ENNReal) := by
    simpa [d] using
      (prob_candidateResponseDist_acceptBoxSet_centeredBounded
        (p := p) (hb := hb) (cfg := cfg)
        (Bh := Bh) (Bb := Bb) (skBound := skBound)
        (bindingFactor := bindingFactor) (c := c) (sk := sk) (κ := κ)
        hB hsk hshift)

  have hmono : Dist.prob d (acceptBoxSet p cfg.localBound) ≤
      Dist.prob d (acceptSet (S := latticeScheme (p := p) hb) cfg) :=
    Dist.prob_mono (d := d)
      (acceptBoxSet_subset_acceptSet (p := p) (hb := hb) (cfg := cfg))

  calc
    ((CenteredBounded.box p.n cfg.localBound).card : ENNReal) /
          ((CenteredBounded.box p.n Bh).card : ENNReal)
        = Dist.prob d (acceptBoxSet p cfg.localBound) := by
            simpa using hbox.symm
    _ ≤ Dist.prob d (acceptSet (S := latticeScheme (p := p) hb) cfg) := hmono
