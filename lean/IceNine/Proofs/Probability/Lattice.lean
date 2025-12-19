/-
# Concrete Distributions for `latticeScheme`

This file provides concrete, “centered bounded” sampling distributions that can
be plugged into the probabilistic assumptions (`openingDist` / `nonceDist`) for
the demo lattice scheme in `IceNine.Instances`.

These are not (yet) claimed to satisfy any security property; they are just
explicit distributions induced by sampling coefficients uniformly from `[-B, B]`.
-/

import IceNine.Instances
import IceNine.Proofs.Probability.CenteredBounded

set_option autoImplicit false

namespace IceNine.Proofs.Probability

noncomputable section

open IceNine.Instances

namespace Lattice

/-- Distribution family for commitment openings in the lattice demo scheme. -/
def openingDist (p : LatticeParams) (B : Nat := p.bound) : DistFamily (Fin p.n → Int) :=
  CenteredBounded.vecFamily p.n B

/-- Distribution family for nonce pairs `(y_hiding, y_binding)` in the lattice demo scheme. -/
def nonceDist (p : LatticeParams) (B : Nat := p.bound) :
    DistFamily ((Fin p.n → Int) × (Fin p.n → Int)) :=
  fun _ => Dist.prod (CenteredBounded.vec p.n B) (CenteredBounded.vec p.n B)

end Lattice

end

end IceNine.Proofs.Probability

