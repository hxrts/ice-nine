/-
# Threshold Signing

Threshold (t-of-n) signing support: coefficient strategies and context management.
Split from Sign.lean for modularity.

See Sign.lean for the full protocol documentation and API guidance.
-/

import IceNine.Protocol.Sign.Core
import Mathlib

namespace IceNine.Protocol

open List

/-!
## Coefficient Strategy

Selects how partial signatures are combined:
- ones: simple sum z = Σ z_i (n-of-n, no field ops needed)
- lagrange: weighted sum z = Σ λ_i·z_i (t-of-n, requires field)
-/

/-- Coefficient strategy: how to combine partial signatures. -/
inductive CoeffStrategy (S : Scheme)
  | ones                                       -- n-of-n: z = Σ z_i
  | lagrange (coeffs : List (LagrangeCoeff S)) -- t-of-n: z = Σ λ_i·z_i

/-- Validity predicate: coefficients align with active signer list. -/
def strategyOK (S : Scheme) [DecidableEq S.PartyId]
  (active : List S.PartyId) : CoeffStrategy S → Prop
  | .ones => True
  | .lagrange coeffs =>
      coeffs.length = active.length ∧ coeffs.map (·.pid) = active

/-- Aggregate using strategy, validating shares against active set. -/
def aggregateWithStrategy
  (S    : Scheme) [DecidableEq S.PartyId]
  (c    : S.Challenge)
  (active : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  (strategy : CoeffStrategy S)
  : Option (Signature S) :=
  if hfrom : ∀ sh ∈ shares, sh.sender ∈ active then
    match strategy with
    | .ones =>
        if hlen : shares.length = active.length then
          some (aggregateSignature S c active commits shares)
        else none
    | .lagrange coeffs =>
        if hlen : shares.length = coeffs.length then
          if hpid : coeffs.map (·.pid) = active then
            some (aggregateSignatureLagrange S c active commits coeffs shares)
          else none
        else none
  else none

/-!
## Threshold Context

Bundles configuration and validity guarantees for threshold signing.
-/

/-- Signing mode: all-parties (n-of-n) or general threshold (t-of-n). -/
inductive SignMode | all | threshold
deriving DecidableEq

/-- Threshold context with proofs of well-formedness. -/
structure ThresholdCtx (S : Scheme) [DecidableEq S.PartyId] where
  active     : Finset S.PartyId
  t          : Nat
  mode       : SignMode
  strategy   : CoeffStrategy S
  card_ge    : t ≤ active.card
  strategy_ok : strategyOK S active.toList strategy

/-- Membership predicate: all shares from declared active set. -/
def sharesFromActive (S : Scheme) [DecidableEq S.PartyId]
  (ctx : ThresholdCtx S) (shares : List (SignShareMsg S)) : Prop :=
  ∀ sh ∈ shares, sh.sender ∈ ctx.active

/-- Decidable instance for sharesFromActive. -/
instance sharesFromActiveDecidable (S : Scheme) [DecidableEq S.PartyId]
  (ctx : ThresholdCtx S) (shares : List (SignShareMsg S))
  : Decidable (sharesFromActive S ctx shares) :=
  inferInstanceAs (Decidable (∀ sh ∈ shares, sh.sender ∈ ctx.active))

/-!
## Context Constructors
-/

/-- Build n-of-n context: threshold = |active|, strategy = ones. -/
def mkAllCtx (S : Scheme) [DecidableEq S.PartyId]
  (active : Finset S.PartyId) : ThresholdCtx S :=
{ active := active,
  t := active.card,
  mode := SignMode.all,
  strategy := CoeffStrategy.ones,
  card_ge := by simp,
  strategy_ok := by trivial }

/-- Build t-of-n context with pre-supplied Lagrange coefficients. -/
def mkThresholdCtx
  (S : Scheme) [DecidableEq S.PartyId]
  (active : Finset S.PartyId)
  (t : Nat)
  (coeffs : List (LagrangeCoeff S))
  (hcard : t ≤ active.card)
  (halign : coeffs.map (·.pid) = active.toList)
  (hlen : coeffs.length = active.toList.length)
  : ThresholdCtx S :=
{ active := active,
  t := t,
  mode := SignMode.threshold,
  strategy := CoeffStrategy.lagrange coeffs,
  card_ge := hcard,
  strategy_ok := by simp [strategyOK, halign, hlen] }

/-- Extract Lagrange coefficients from context. -/
noncomputable def coeffsFromCtx
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId] [DecidableEq S.Scalar]
  (ctx : ThresholdCtx S)
  (pidToScalar : S.PartyId → S.Scalar) : List (LagrangeCoeff S) :=
  ctx.active.toList.map (fun pid =>
    { pid := pid, lambda := lagrangeCoeffAtZero S pidToScalar ctx.active.toList pid })

/-- Build t-of-n context by computing fresh Lagrange coefficients. -/
noncomputable def mkThresholdCtxComputed
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId] [DecidableEq S.Scalar]
  (active : Finset S.PartyId)
  (t : Nat)
  (pidToScalar : S.PartyId → S.Scalar)
  (hcard : t ≤ active.card) : ThresholdCtx S :=
  let coeffs := active.toList.map (fun pid =>
    { pid := pid, lambda := lagrangeCoeffAtZero S pidToScalar active.toList pid })
  have hlen : coeffs.length = active.toList.length := by simp [coeffs]
  have hpid : coeffs.map (fun (c : LagrangeCoeff S) => c.pid) = active.toList := by
    simp only [coeffs, List.map_map, Function.comp_def]
    exact List.map_id _
  mkThresholdCtx S active t coeffs hcard hpid hlen

/-- Refresh context with fresh coefficients. -/
noncomputable def refreshThresholdCtx
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId] [DecidableEq S.Scalar]
  (pidToScalar : S.PartyId → S.Scalar)
  (ctx : ThresholdCtx S) : ThresholdCtx S :=
  mkThresholdCtxComputed S ctx.active ctx.t pidToScalar ctx.card_ge

/-!
## Context-Based Aggregation
-/

/-- Aggregate using context's strategy after membership validation. -/
noncomputable def aggregateSignatureWithCtx
  (S    : Scheme) [DecidableEq S.PartyId]
  (c    : S.Challenge)
  (ctx  : ThresholdCtx S)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  : Option (Signature S) :=
  if _hfrom : sharesFromActive S ctx shares then
    aggregateWithStrategy S c ctx.active.toList commits shares ctx.strategy
  else
    none

/-- Direct Lagrange aggregation using context's active set. -/
noncomputable def aggregateSignatureLagrangeThresh
  (S    : Scheme) [DecidableEq S.PartyId]
  (c    : S.Challenge)
  (ctx  : ThresholdCtx S)
  (commits : List S.Commitment)
  (coeffs : List (LagrangeCoeff S))
  (shares : List (SignShareMsg S))
  : Signature S :=
  aggregateSignatureLagrange S c ctx.active.toList commits coeffs shares

end IceNine.Protocol
