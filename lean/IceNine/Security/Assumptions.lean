/-
# Security assumptions and statements

We package the abstract assumptions (hash RO, binding commitments, norm bounds)
and state threshold UF-CMA and liveness theorems parametrized by them.
-/

import IceNine.Protocol.Core
import IceNine.Protocol.Sign
import IceNine.Protocol.DKGCore

namespace IceNine.Security

open IceNine.Protocol

structure Assumptions (S : Scheme) where
  hashRO : Prop
  commitBinding : Prop := S.commitCollisionResistant
  normLeakageBound : Prop
  corruptionBound : Nat

/-- Threshold UF-CMA statement placeholder, parameterized by assumptions. -/
def thresholdUFcma (S : Scheme) (A : Assumptions S) : Prop := A.hashRO ∧ A.commitBinding ∧ A.normLeakageBound

/-- Liveness/abort statement placeholder. -/
def livenessOrAbort (S : Scheme) (A : Assumptions S) : Prop := True

end IceNine.Security
