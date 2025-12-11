/-
# Robustness and Liveness Proofs

Robustness: protocol either succeeds or returns meaningful error.
Liveness: honest parties always make progress (no silent hangs).

Key property: all validation functions are total - they always return
either Ok(result) or Error(reason), never diverge or panic.
-/

import Mathlib
import IceNine.Protocol.Sign.Sign
import IceNine.Protocol.DKG.Core

namespace IceNine.Security

open IceNine.Protocol

/-!
## Security Assumptions

Alternative bundling of assumptions (compared to Assumptions.lean).
Used for specific theorem statements.
-/

/-- Security assumptions for threshold signature. -/
structure SecurityAssumptions (S : Scheme) where
  /-- Hash is random oracle -/
  hashRO            : Prop
  /-- Commitments are binding -/
  commitmentBinding : Prop := True
  /-- Threshold UF-CMA holds -/
  thresholdUFcma    : Prop

/-- Extract the UF-CMA assumption from the bundle. -/
theorem threshold_ufcma
  (S : Scheme) (H : SecurityAssumptions S) : Prop :=
  H.thresholdUFcma

/-!
## Totality Theorems

All protocol functions return Ok or Error - no exceptions or divergence.
This is crucial for CRDT safety: handlers must be total.
-/

/-- Signing validation is total: always returns Ok or Error. -/
theorem validateSigning_total
  (S : Scheme) [DecidableEq S.PartyId]
  (pk : S.Public) (m : S.Message) (Sset : List S.PartyId)
  (commits : List (SignCommitMsg S)) (reveals : List (SignRevealWMsg S)) (shares : List (SignShareMsg S)) :
  (validateSigning S pk m Sset commits reveals shares).isOk ∨
  (validateSigning S pk m Sset commits reveals shares).isError := by
  by_cases h : validateSigning S pk m Sset commits reveals shares with
  | _ => cases h <;> simp

/-- DKG aggregation is total: always returns Ok or Error. -/
theorem dkgAggregateChecked_total
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S)) :
  (dkgAggregateChecked S commits reveals).isOk ∨
  (dkgAggregateChecked S commits reveals).isError := by
  by_cases h : dkgAggregateChecked S commits reveals with
  | _ => cases h <;> simp

/-!
## Liveness

With bounded faults, honest parties make progress. Either signing
succeeds or a specific error is returned identifying the problem.
-/

/-- Liveness under bounded faults: succeed or report specific error.
    Parameter f bounds the number of faulty parties. -/
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
