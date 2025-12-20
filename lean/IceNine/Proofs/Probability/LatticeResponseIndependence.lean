/-
# Response Independence for the Lattice Demo Scheme

This file packages the centered-bounded acceptance and candidate-response
indistinguishability lemmas into a concrete `ResponseIndependence` construction
for the demo `latticeScheme`, under explicit boundedness conditions.
-/

import IceNine.Proofs.Core.Assumptions
import IceNine.Proofs.Probability.LatticeRejectionAccept
import IceNine.Proofs.Probability.LatticeRejectionIndist

set_option autoImplicit false

namespace IceNine.Proofs.Probability

noncomputable section

open IceNine.Instances
open IceNine.Protocol
open IceNine.Protocol.ThresholdConfig

namespace Lattice

/-- Secrets with coefficients bounded by `skBound`. -/
def secretOK (p : LatticeParams) (skBound : Nat) : Set (Fin p.n → Int) :=
  { sk | ∀ i, Int.natAbs (sk i) ≤ skBound }

/-- Admissible public parameters ensuring the uniform margin used in acceptance proofs. -/
def publicOK (cfg : ThresholdConfig) (Bh Bb skBound : Nat) : Int → Int → Prop :=
  fun bindingFactor c =>
    cfg.localBound ≤ Bh ∧
      Int.natAbs bindingFactor * Bb + Int.natAbs c * skBound ≤ Bh - cfg.localBound


/-- A centered-bounded nonce distribution family for the lattice demo scheme.

We sample a *binding* nonce uniformly from `[-Bb, Bb]^n` and a *hiding* nonce
uniformly from `[-Bh, Bh]^n`, then swap into the protocol’s `(hiding, binding)`
order.

This is the distribution used by `LatticeRejectionAccept` / `LatticeRejectionIndist`. -/
def nonceDistCenteredBounded (p : LatticeParams) (Bh Bb : Nat) :
    DistFamily ((Fin p.n → Int) × (Fin p.n → Int)) :=
  nonceDistSwapProd p (fun _ => Bh) (fun _ => CenteredBounded.vec p.n Bb)

/-- Construct `ResponseIndependence` for the lattice demo scheme from explicit bounds.

This packages:
- an explicit lower bound on `Pr[acceptSet]` (via `LatticeRejectionAccept`), and
- candidate-response indistinguishability (via `LatticeRejectionIndist`, assuming
  the explicit `candidateShiftError` bound is negligible).

The result is *non-vacuous*: all assumptions are stated as concrete boundedness
conditions rather than global axioms.
-/
def responseIndependence_centeredBounded
    (p : LatticeParams) (hb : HashBinding)
    (cfg : ThresholdConfig)
    (Bh Bb skBound : Nat)
    (hNeg :
      ∀ (bindingFactor : Int) (c : Int) (s₁ s₂ : Fin p.n → Int),
        publicOK cfg Bh Bb skBound bindingFactor c →
          s₁ ∈ secretOK p skBound →
          s₂ ∈ secretOK p skBound →
            Negligible (candidateShiftError p (fun _ => Bh) c s₁ s₂)) :
    ResponseIndependence (S := latticeScheme (p := p) hb) := by
  classical
  let nonceDist : DistFamily ((Fin p.n → Int) × (Fin p.n → Int)) :=
    nonceDistCenteredBounded p Bh Bb
  let accept_lb : ENNReal :=
    ((CenteredBounded.box p.n cfg.localBound).card : ENNReal) /
      ((CenteredBounded.box p.n Bh).card : ENNReal)

  refine
    { cfg := cfg
      nonceDist := nonceDist
      secretOK := secretOK p skBound
      publicOK := publicOK cfg Bh Bb skBound
      accept_lb := accept_lb
      accept_lb_ne_zero := ?_
      accept_prob_ge := ?_
      candidate_indist := ?_ }

  · have hnum0 : ((CenteredBounded.box p.n cfg.localBound).card : ENNReal) ≠ 0 := by
      have hpos : 0 < (CenteredBounded.box p.n cfg.localBound).card :=
        Finset.card_pos.2 (CenteredBounded.box_nonempty p.n cfg.localBound)
      exact_mod_cast (Nat.ne_of_gt hpos)
    have hdenTop : ((CenteredBounded.box p.n Bh).card : ENNReal) ≠ (⊤ : ENNReal) := by
      exact (ENNReal.natCast_ne_top (CenteredBounded.box p.n Bh).card)
    have : accept_lb ≠ 0 := (ENNReal.div_ne_zero).2 ⟨hnum0, hdenTop⟩
    simpa [accept_lb] using this

  · intro bindingFactor c s κ hpub hs
    have hB : cfg.localBound ≤ Bh := hpub.1
    have hshift :
        Int.natAbs bindingFactor * Bb + Int.natAbs c * skBound ≤ Bh - cfg.localBound :=
      hpub.2
    have hsk : ∀ i, Int.natAbs (s i) ≤ skBound := hs
    simpa [accept_lb, nonceDist, nonceDistCenteredBounded] using
      (prob_candidateResponseDist_acceptSet_ge_centeredBounded
        (p := p) (hb := hb) (cfg := cfg)
        (Bh := Bh) (Bb := Bb) (skBound := skBound)
        (bindingFactor := bindingFactor) (c := c) (sk := s) (κ := κ)
        hB hsk hshift)

  · intro bindingFactor c s₁ s₂ hpub hs₁ hs₂
    have hNeg' : Negligible (candidateShiftError p (fun _ => Bh) c s₁ s₂) :=
      hNeg bindingFactor c s₁ s₂ hpub hs₁ hs₂
    simpa [nonceDist, nonceDistCenteredBounded] using
      (indistinguishable_candidateResponseDist_centeredBounded
        (p := p) (hb := hb) (B := fun _ => Bh)
        (bindingNonceDist := fun _ => CenteredBounded.vec p.n Bb)
        (bindingFactor := bindingFactor) (c := c)
        (sk₁ := s₁) (sk₂ := s₂)
        hNeg')
