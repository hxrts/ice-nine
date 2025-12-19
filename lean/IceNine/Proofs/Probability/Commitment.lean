/-
# Probability Layer: Commitment Sampling

`Scheme.commit` is deterministic, but commitment *hiding* is about the
distribution induced by sampling a random opening and applying `commit`.

This file defines that induced distribution as a `DistFamily`.
-/

import IceNine.Protocol.Core.Core
import IceNine.Proofs.Probability.Dist

set_option autoImplicit false

namespace IceNine.Proofs.Probability

noncomputable section

open IceNine.Protocol

/-- Distribution of commitments induced by sampling an opening and committing to `x`. -/
def commitDist (S : Scheme) (openingDist : DistFamily S.Opening) (x : S.Public) :
    DistFamily S.Commitment :=
  fun κ => Dist.map (fun o => S.commit x o) (openingDist κ)

end

end IceNine.Proofs.Probability
