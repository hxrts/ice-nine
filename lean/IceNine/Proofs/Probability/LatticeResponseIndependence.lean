/-
# Response Independence for the Lattice Demo Scheme

This file packages the centered-bounded acceptance and candidate-response
indistinguishability lemmas into a concrete `ResponseIndependence` construction
for the demo `latticeScheme`, under explicit boundedness and growth conditions.
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

/-- Admissible public parameters ensuring the uniform margin used in acceptance proofs.

We phrase the margin conditions uniformly in `κ` so that a single `publicOK` hypothesis can be
used in the `ResponseIndependence` interface, which quantifies over all `κ`.
-/
def publicOK (cfg : Nat → ThresholdConfig) (Bh Bb : Nat → Nat) (skBound : Nat) : Int → Int → Prop :=
  fun bindingFactor c =>
    (∀ κ, (cfg κ).localBound ≤ Bh κ) ∧
      (∀ κ,
        Int.natAbs bindingFactor * Bb κ + Int.natAbs c * skBound ≤
          Bh κ - (cfg κ).localBound)

/-- A centered-bounded nonce distribution family for the lattice demo scheme.

We sample a *binding* nonce uniformly from `[-Bb κ, Bb κ]^n` and a *hiding* nonce uniformly from
`[-Bh κ, Bh κ]^n`, then swap into the protocol’s `(hiding, binding)` order.

This is the distribution used by `LatticeRejectionAccept` / `LatticeRejectionIndist`.
-/
def nonceDistCenteredBounded (p : LatticeParams) (Bh Bb : Nat → Nat) :
    DistFamily ((Fin p.n → Int) × (Fin p.n → Int)) :=
  nonceDistSwapProd p Bh (fun κ => CenteredBounded.vec p.n (Bb κ))

/-- Construct `ResponseIndependence` for the lattice demo scheme from explicit bounds.

This packages:
- an explicit lower bound on `Pr[acceptSet]` (via `LatticeRejectionAccept`), and
- candidate-response indistinguishability (via `LatticeRejectionIndist`).

For the statistical part we assume:
- `SuperpolyGrowth Bh` to make the explicit shift error negligible, and
- an inverse-polynomial bound on the acceptance lower bound (so conditioning preserves negligibility).
-/
def responseIndependence_centeredBounded
    (p : LatticeParams) (hb : HashBinding)
    (cfg : Nat → ThresholdConfig)
    (Bh Bb : Nat → Nat)
    (skBound : Nat)
    (hBh : SuperpolyGrowth Bh)
    (hAccInvPoly :
      ∃ d : Nat, ∀ᶠ κ in Filter.atTop,
        (((CenteredBounded.box p.n (Bh κ)).card : ENNReal) /
            ((CenteredBounded.box p.n (cfg κ).localBound).card : ENNReal))
          ≤ (κ : ENNReal) ^ d) :
    ResponseIndependence (S := latticeScheme (p := p) hb) := by
  classical

  let nonceDist : DistFamily ((Fin p.n → Int) × (Fin p.n → Int)) :=
    nonceDistCenteredBounded p Bh Bb

  -- Per-`κ` acceptance lower bound (exact for the centered-box event).
  let accept_lb : Nat → ENNReal :=
    fun κ =>
      ((CenteredBounded.box p.n (cfg κ).localBound).card : ENNReal) /
        ((CenteredBounded.box p.n (Bh κ)).card : ENNReal)

  refine
    { cfg := cfg
      nonceDist := nonceDist
      secretOK := secretOK p skBound
      publicOK := publicOK cfg Bh Bb skBound
      accept_lb := accept_lb
      accept_lb_ne_zero := ?_
      accept_inv_poly := ?_
      accept_prob_ge := ?_
      candidate_indist := ?_ }

  · intro κ
    have hnum0 : ((CenteredBounded.box p.n (cfg κ).localBound).card : ENNReal) ≠ 0 := by
      have hpos : 0 < (CenteredBounded.box p.n (cfg κ).localBound).card :=
        Finset.card_pos.2 (CenteredBounded.box_nonempty p.n (cfg κ).localBound)
      exact_mod_cast (Nat.ne_of_gt hpos)
    have hdenTop : ((CenteredBounded.box p.n (Bh κ)).card : ENNReal) ≠ (⊤ : ENNReal) := by
      exact (ENNReal.natCast_ne_top (CenteredBounded.box p.n (Bh κ)).card)
    have : accept_lb κ ≠ 0 := (ENNReal.div_ne_zero).2 ⟨hnum0, hdenTop⟩
    simpa [accept_lb] using this

  · -- Turn the provided bound into the shape required by `ResponseIndependence`.
    rcases hAccInvPoly with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    filter_upwards [hd] with κ hκ
    -- `accept_lb κ` is the reciprocal of the fraction in `hAccInvPoly`.
    have hinv : (accept_lb κ)⁻¹ =
        (((CenteredBounded.box p.n (Bh κ)).card : ENNReal) /
          ((CenteredBounded.box p.n (cfg κ).localBound).card : ENNReal)) := by
      -- Use `ENNReal.inv_div` and the fact that these cardinals are finite and nonzero.
      set a : ENNReal := ((CenteredBounded.box p.n (cfg κ).localBound).card : ENNReal)
      set b : ENNReal := ((CenteredBounded.box p.n (Bh κ)).card : ENNReal)
      have haTop : a ≠ (⊤ : ENNReal) := by
        simp [a, ENNReal.natCast_ne_top]
      have hbTop : b ≠ (⊤ : ENNReal) := by
        simp [b, ENNReal.natCast_ne_top]
      have ha0 : a ≠ 0 := by
        dsimp [a]
        have hpos : 0 < (CenteredBounded.box p.n (cfg κ).localBound).card :=
          Finset.card_pos.2 (CenteredBounded.box_nonempty p.n (cfg κ).localBound)
        exact_mod_cast (Nat.ne_of_gt hpos)
      have hb0 : b ≠ 0 := by
        dsimp [b]
        have hpos : 0 < (CenteredBounded.box p.n (Bh κ)).card :=
          Finset.card_pos.2 (CenteredBounded.box_nonempty p.n (Bh κ))
        exact_mod_cast (Nat.ne_of_gt hpos)
      -- Rewrite `accept_lb` as `a / b` and apply the inversion lemma.
      have : (a / b)⁻¹ = b / a :=
        ENNReal.inv_div (htop := Or.inl hbTop) (hzero := Or.inl hb0)
      -- Unfold `accept_lb` and finish by rewriting.
      simpa [accept_lb, a, b] using this
    simpa [hinv] using hκ

  · intro bindingFactor c s κ hpub hs
    have hB : (cfg κ).localBound ≤ Bh κ := (hpub.1 κ)
    have hshift :
        Int.natAbs bindingFactor * Bb κ + Int.natAbs c * skBound ≤
          Bh κ - (cfg κ).localBound := (hpub.2 κ)
    have hsk : ∀ i, Int.natAbs (s i) ≤ skBound := hs
    -- Use the acceptance lower bound lemma.
    simpa [accept_lb, nonceDist, nonceDistCenteredBounded] using
      (prob_candidateResponseDist_acceptSet_ge_centeredBounded
        (p := p) (hb := hb) (cfg := cfg κ)
        (Bh := Bh) (Bb := Bb) (skBound := skBound)
        (bindingFactor := bindingFactor) (c := c) (sk := s) (κ := κ)
        hB hsk hshift)

  · intro bindingFactor c s₁ s₂ _hpub hs₁ hs₂
    -- Negligibility of the explicit shift error follows from `SuperpolyGrowth Bh`.
    have hNeg : Negligible (candidateShiftError p Bh c s₁ s₂) :=
      negligible_candidateShiftError_of_superpoly (p := p) (B := Bh) (c := c) (sk₁ := s₁) (sk₂ := s₂) hBh
    simpa [nonceDist, nonceDistCenteredBounded] using
      (indistinguishable_candidateResponseDist_centeredBounded
        (p := p) (hb := hb) (B := Bh)
        (bindingNonceDist := fun κ => CenteredBounded.vec p.n (Bb κ))
        (bindingFactor := bindingFactor) (c := c)
        (sk₁ := s₁) (sk₂ := s₂)
        hNeg)

end Lattice

end

end IceNine.Proofs.Probability
