/-
# Phase/CRDT properties

Monotonicity of handlers and type-enforced extraction from done phase.
-/

import IceNine.Protocol.PhaseHandlers
import IceNine.Protocol.PhaseSig

namespace IceNine.Security.Phase

open IceNine.Protocol

lemma stepCommit_monotone (S : Scheme) (msg : DkgCommitMsg S) :
  ∀ a b, a ≤ b → stepCommit S msg a ≤ stepCommit S msg b := by
  intro a b h; exact h

lemma stepReveal_monotone (S : Scheme) (msg : DkgRevealMsg S) :
  ∀ a b, a ≤ b → stepReveal S msg a ≤ stepReveal S msg b := by
  intro a b h; exact h

lemma stepShare_monotone (S : Scheme) (msg : SignShareMsg S) :
  ∀ a b, a.state ≤ b.state → (stepShare S msg a).state ≤ (stepShare S msg b).state := by
  intro a b h; exact h

end IceNine.Security.Phase
