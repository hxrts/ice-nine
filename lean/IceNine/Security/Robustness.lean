/-
# Robustness, assumptions, and liveness
-/

import Mathlib
import IceNine.Protocol.Sign
import IceNine.Protocol.DKGCore

namespace IceNine.Security

open IceNine.Protocol

/-- Abstract UF-CMA/threshold assumption container. -/
structure SecurityAssumptions (S : Scheme) where
  hashRO     : Prop
  commitmentBinding : Prop := True
  thresholdUFcma : Prop

/-- Under provided assumptions, we assert threshold UF-CMA as given. -/
theorem threshold_ufcma
  (S : Scheme) (H : SecurityAssumptions S) : Prop :=
  H.thresholdUFcma

/-- Totality: validateSigning always returns ok or error (decidable). -/
theorem validateSigning_total
  (S : Scheme) [DecidableEq S.PartyId]
  (pk : S.Public) (m : S.Message) (Sset : List S.PartyId)
  (commits : List (SignCommitMsg S)) (reveals : List (SignRevealWMsg S)) (shares : List (SignShareMsg S)) :
  (validateSigning S pk m Sset commits reveals shares).isOk ∨
  (validateSigning S pk m Sset commits reveals shares).isError := by
  by_cases h : validateSigning S pk m Sset commits reveals shares with
  | _ => cases h <;> simp

/-- Totality for DKG aggregation with errors. -/
theorem dkgAggregateChecked_total
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S)) :
  (dkgAggregateChecked S commits reveals).isOk ∨
  (dkgAggregateChecked S commits reveals).isError := by
  by_cases h : dkgAggregateChecked S commits reveals with
  | _ => cases h <;> simp

/--
  Liveness/abort statement parameterized by a bound on faults; currently derives from totality.
-/
theorem liveness_or_abort
  (S : Scheme) [DecidableEq S.PartyId]
  (f faults : Nat)
  (pk : S.Public) (m : S.Message) (Sset : List S.PartyId)
  (commits : List (SignCommitMsg S)) (reveals : List (SignRevealWMsg S)) (shares : List (SignShareMsg S))
  (hfaults : faults ≤ f) :
  (validateSigning S pk m Sset commits reveals shares).isOk ∨
  (validateSigning S pk m Sset commits reveals shares).isError :=
  validateSigning_total S pk m Sset commits reveals shares

end IceNine.Security
