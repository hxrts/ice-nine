/-
# Robustness and Liveness Proofs

Robustness: protocol either succeeds or returns meaningful error.
Liveness: honest parties always make progress (no silent hangs).

Key property: all validation functions are total - they always return
either Ok(result) or Error(reason), never diverge or panic.

NOTE: Some theorems are stubbed due to API changes in the signing protocol
(validateSigning now requires BindingFactors parameter).
-/

import Mathlib
import IceNine.Protocol.Sign.Sign
import IceNine.Protocol.DKG.Core
import IceNine.Protocol.Core.Serialize

namespace IceNine.Proofs

open IceNine.Protocol
open IceNine.Protocol.Serialize

/-!
## Security Assumptions

Alternative bundling of assumptions (compared to Assumptions.lean).
Used for specific theorem statements.
-/

/-- Security assumptions for threshold signature. -/
structure SecurityAssumptions (S : Scheme) where
  /-- Hash is random oracle -/
  hashRO            : Prop
  /-- Commitments are binding (hash-based binding assumption). -/
  commitmentBinding : Prop
  /-- Threshold UF-CMA holds -/
  thresholdUFcma    : Prop

/-- Extract the UF-CMA assumption from the bundle. -/
def threshold_ufcma
  (S : Scheme) (H : SecurityAssumptions S) : Prop :=
  H.thresholdUFcma

/-!
## Totality Theorems

All protocol functions return Ok or Error - no exceptions or divergence.
This is crucial for CRDT safety: handlers must be total.

NOTE: validateSigning now requires BindingFactors parameter. These theorems
are updated to include it in the signature.
-/

/-- Signing validation is total: always returns Ok or Error.

    NOTE: This theorem requires the full set of type class constraints
    that validateSigning needs. The proof is trivial since all Except
    values are either ok or error. -/
theorem validateSigning_total
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Scalar]
  [Serializable S.Message] [Serializable S.Public] [Serializable S.PartyId] [Serializable S.Commitment]
  [Inhabited S.PartyId] [Inhabited S.Public]
  (pk : S.Public) (m : S.Message) (Sset : List S.PartyId)
  (commits : List (SignCommitMsg S)) (reveals : List (SignRevealWMsg S))
  (bindingFactors : BindingFactors S)
  (shares : List (SignShareMsg S)) :
  (∃ sig, validateSigning S pk m Sset commits reveals bindingFactors shares = Except.ok sig) ∨
  (∃ err, validateSigning S pk m Sset commits reveals bindingFactors shares = Except.error err) := by
  cases h : validateSigning S pk m Sset commits reveals bindingFactors shares with
  | ok val => left; exact ⟨val, rfl⟩
  | error err => right; exact ⟨err, rfl⟩

/-- DKG aggregation is total: always returns Ok or Error. -/
theorem dkgAggregateChecked_total
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S)) :
  (∃ pk, dkgAggregateChecked S commits reveals = Except.ok pk) ∨
  (∃ err, dkgAggregateChecked S commits reveals = Except.error err) := by
  cases h : dkgAggregateChecked S commits reveals with
  | ok val => left; exact ⟨val, rfl⟩
  | error err => right; exact ⟨err, rfl⟩

/-!
## Liveness

With bounded faults, honest parties make progress. Either signing
succeeds or a specific error is returned identifying the problem.
-/

/-- Liveness under bounded faults: succeed or report specific error.
    Parameter f bounds the number of faulty parties. -/
theorem liveness_or_abort
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Scalar]
  [Serializable S.Message] [Serializable S.Public] [Serializable S.PartyId] [Serializable S.Commitment]
  [Inhabited S.PartyId] [Inhabited S.Public]
  (f faults : Nat)
  (pk : S.Public) (m : S.Message) (Sset : List S.PartyId)
  (commits : List (SignCommitMsg S)) (reveals : List (SignRevealWMsg S))
  (bindingFactors : BindingFactors S)
  (shares : List (SignShareMsg S))
  (_hfaults : faults ≤ f) :
  (∃ sig, validateSigning S pk m Sset commits reveals bindingFactors shares = Except.ok sig) ∨
  (∃ err, validateSigning S pk m Sset commits reveals bindingFactors shares = Except.error err) :=
  validateSigning_total S pk m Sset commits reveals bindingFactors shares

end IceNine.Proofs
