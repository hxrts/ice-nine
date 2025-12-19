/-
# Probability Layer: Centered Bounded Sampling

Dilithium-style lattice schemes sample secrets/nonces/openings from *centered bounded*
distributions (e.g. coefficients in `[-η, η]`).

This module provides simple concrete samplers as `Dist` values, built from:
- uniform distributions on finite types, and
- `Dist.map` into the desired (potentially infinite) carrier type like `Int` or
  `Fin n → Int`.

These are intended to be plugged into `openingDist` / `nonceDist` later.
-/

import IceNine.Proofs.Probability.Dist

set_option autoImplicit false

namespace IceNine.Proofs.Probability

noncomputable section

namespace CenteredBounded

/-- Map an index `i ∈ {0,…,2B}` to an integer in `[-B, B]`. -/
def finToCenteredInt (B : Nat) (i : Fin (2 * B + 1)) : Int :=
  (i.val : Int) - (B : Int)

/-- Centered bounded distribution on `Int`, uniform on `[-B, B]`. -/
def int (B : Nat) : Dist Int :=
  Dist.map (finToCenteredInt B) (Dist.uniform (Fin (2 * B + 1)))

/-- Centered bounded distribution on `Fin n → Int`, coefficientwise uniform on `[-B, B]`.

Implementation note: this is the pushforward of the uniform distribution on the finite type
`Fin n → Fin (2*B+1)`. -/
def vec (n B : Nat) : Dist (Fin n → Int) :=
  Dist.map
    (fun f : Fin n → Fin (2 * B + 1) => fun i => finToCenteredInt B (f i))
    (Dist.uniform (Fin n → Fin (2 * B + 1)))

/-- κ-agnostic centered bounded coefficient family (useful for fixed-parameter schemes). -/
abbrev intFamily (B : Nat) : DistFamily Int :=
  fun _ => int B

/-- κ-agnostic centered bounded vector family (useful for fixed-parameter schemes). -/
abbrev vecFamily (n B : Nat) : DistFamily (Fin n → Int) :=
  fun _ => vec n B

end CenteredBounded

end

end IceNine.Proofs.Probability

