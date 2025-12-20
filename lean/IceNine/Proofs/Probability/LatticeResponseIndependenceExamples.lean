/-
# Lattice Response Independence: Parameter Bundles and Examples

This file contains convenience bundles and a toy instantiation for
`Lattice.responseIndependence_centeredBounded`.

Keeping these examples separate avoids polluting the core API/lemmas.
-/

import IceNine.Proofs.Probability.LatticeResponseIndependence

set_option autoImplicit false

namespace IceNine.Proofs.Probability

noncomputable section

open IceNine.Instances
open IceNine.Protocol
open IceNine.Protocol.ThresholdConfig

namespace Lattice

/-- Parameter bundle for constructing response independence for the lattice demo scheme
under the centered-bounded nonce model.

This avoids threading several functions/hypotheses (`cfg`, `Bh`, `Bb`, bounds, growth) through every call site. -/
structure CenteredBoundedRIParams (p : LatticeParams) where
  cfg : Nat → ThresholdConfig
  Bh : Nat → Nat
  Bb : Nat → Nat
  skBound : Nat
  Bh_superpoly : SuperpolyGrowth Bh
  gap_poly :
    ∃ d0 : Nat, ∀ᶠ κ in Filter.atTop,
      (Bh κ - (cfg κ).localBound) ≤ κ ^ d0

/-- Build `ResponseIndependence` from a `CenteredBoundedRIParams` bundle. -/
def CenteredBoundedRIParams.responseIndependence
    (p : LatticeParams) (hb : HashBinding)
    (P : CenteredBoundedRIParams p) :
    ResponseIndependence (S := latticeScheme (p := p) hb) :=
  responseIndependence_centeredBounded
    (p := p) (hb := hb)
    (cfg := P.cfg)
    (Bh := P.Bh) (Bb := P.Bb)
    (skBound := P.skBound)
    (hBh := P.Bh_superpoly)
    (hGapPoly := P.gap_poly)

namespace Example

/-- A super-polynomially growing hiding bound: `Bh κ = κ^κ`. -/
def Bh : Nat → Nat := fun κ => κ ^ κ

/-- `Bh` dominates every fixed polynomial. -/
theorem Bh_superpoly : SuperpolyGrowth Bh := by
  intro n
  filter_upwards [Filter.eventually_ge_atTop (n + 1)] with κ hκ
  have hkpos : 0 < κ := Nat.lt_of_lt_of_le (Nat.succ_pos n) hκ
  -- For `κ ≥ n+1`, monotonicity in the exponent gives `κ^(n+1) ≤ κ^κ`.
  exact Nat.pow_le_pow_right hkpos hκ

/-- A toy `ThresholdConfig` family whose local bound is `Bh κ - κ`.

We keep `maxSigners = 1` so `localBound = globalBound` definitionally. -/
def cfg : Nat → ThresholdConfig := fun κ =>
  ThresholdConfig.create 1 (Bh κ - κ) (t := 1) (maxSigners := 1)

/-- The gap `Bh κ - (cfg κ).localBound` is polynomially bounded (in fact, ≤ κ). -/
theorem gap_poly :
    ∃ d0 : Nat, ∀ᶠ κ in Filter.atTop,
      (Bh κ - (cfg κ).localBound) ≤ κ ^ d0 := by
  refine ⟨1, ?_⟩
  refine (Filter.Eventually.of_forall ?_)
  intro κ
  -- `localBound = Bh κ - κ` for our toy config.
  have hlocal : (cfg κ).localBound = Bh κ - κ := by
    simp [cfg, ThresholdConfig.create]
  -- Use `a - (a - b) ≤ b` (via `sub_le_iff_le_add`) with `b = κ`.
  -- First show `Bh κ ≤ (Bh κ - κ) + κ`.
  have hle : Bh κ ≤ (Bh κ - κ) + κ := by
    -- `a - b + b = max a b ≥ a`.
    simp [Nat.sub_add_eq_max]
  -- Turn it into the desired subtraction inequality.
  have hsub : Bh κ - (Bh κ - κ) ≤ κ := (Nat.sub_le_iff_le_add').2 hle
  -- Finish.
  simpa [hlocal, pow_one] using hsub

/-- A simple binding-nonce bound (linear in `κ`). -/
def Bb : Nat → Nat := fun κ => κ

/-- Package the example bounds into `CenteredBoundedRIParams`. -/
def params (p : LatticeParams) (skBound : Nat) : CenteredBoundedRIParams p :=
  { cfg := cfg
    Bh := Bh
    Bb := Bb
    skBound := skBound
    Bh_superpoly := Bh_superpoly
    gap_poly := gap_poly }

/-- A concrete `ResponseIndependence` instance obtained from the example parameter family. -/
def responseIndependence (p : LatticeParams) (hb : HashBinding) (skBound : Nat) :
    ResponseIndependence (S := latticeScheme (p := p) hb) :=
  (CenteredBoundedRIParams.responseIndependence (p := p) (hb := hb) (P := params p skBound))

end Example

end Lattice

end

end IceNine.Proofs.Probability
