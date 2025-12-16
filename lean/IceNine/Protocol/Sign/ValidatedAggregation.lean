/-
# Validated Aggregation

Per-share validation during signature aggregation for local rejection.
Validates each partial signature before aggregation and collects blame
for invalid shares.

## Key Behavior

With local rejection, aggregation validates shares against the local bound:
1. Each share z_i must have ‖z_i‖∞ ≤ localBound
2. Each share must satisfy the algebraic relation A(z_i) = w_eff_i + c·pk_i
3. Invalid shares are rejected (not cause for global restart)
4. Blame is collected according to ProtocolConfig

## Guarantee

If we receive at least `threshold` valid shares, the aggregate signature
is guaranteed to satisfy the global bound (by construction).
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.Core.ThresholdConfig
import IceNine.Protocol.Core.NormBounded
import IceNine.Protocol.Core.Error
import IceNine.Protocol.Sign.Types
import IceNine.Protocol.Sign.Core
import Mathlib

set_option autoImplicit false

namespace IceNine.Protocol.ValidatedAggregation

open IceNine.Protocol
open IceNine.Protocol.ThresholdConfig
open IceNine.Protocol.NormBounded
open IceNine.Protocol.Error

/-!
## Binding Factor Storage

Type alias for binding factor lookup.
-/

/-- Binding factors for a signing session, keyed by party ID. -/
structure BindingFactors (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId] where
  /-- Map from party ID to binding factor -/
  factors : Std.HashMap S.PartyId S.Scalar

/-- Create empty binding factors -/
def BindingFactors.empty (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId] : BindingFactors S :=
  { factors := {} }

/-- Add a binding factor -/
def BindingFactors.add {S : Scheme}
    [BEq S.PartyId] [Hashable S.PartyId]
    (bf : BindingFactors S) (pid : S.PartyId) (rho : S.Scalar) : BindingFactors S :=
  { factors := bf.factors.insert pid rho }

/-- Get a binding factor -/
def BindingFactors.get {S : Scheme}
    [BEq S.PartyId] [Hashable S.PartyId]
    (bf : BindingFactors S) (pid : S.PartyId) : Option S.Scalar :=
  bf.factors.get? pid

/-- Create binding factors from list -/
def BindingFactors.fromList (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    (factors : List (S.PartyId × S.Scalar)) : BindingFactors S :=
  { factors := factors.foldl (fun m (p, r) => m.insert p r) {} }

/-!
## Pure Validation Operations (ValidationOp Namespace)

Following the effect pattern from NonceLifecycle.lean.
-/

namespace ValidationOp

variable {S : Scheme}

/-- Validate a single partial signature (pure).

    Checks:
    1. Norm bound: ‖z_i‖∞ ≤ B_local
    2. Algebraic validity: A(z_i) = w_eff_i + c · pk_i (optional)

    Bad shares are REJECTED, not cause for global restart.

    **Inputs**:
    - `cfg`: Threshold configuration
    - `share`: The partial signature message
    - `commitment`: The commitment message from round 1
    - `pkShare`: The party's public key share
    - `challenge`: The Fiat-Shamir challenge
    - `bindingFactor`: The binding factor ρ_i

    **Returns**: `ok ()` if valid, `error` with blame info if invalid. -/
def validateShare [NormBounded S.Secret] [DecidableEq S.Public]
    [AddCommGroup S.Public] [Module S.Scalar S.Public]
    [SMul S.Challenge S.Public]
    (cfg : ThresholdConfig)
    (share : SignShareMsg S)
    (commitment : SignCommitMsg S)
    (pkShare : S.Public)
    (challenge : S.Challenge)
    (bindingFactor : S.Scalar)
    : Except (ShareValidationError S.PartyId) Unit :=
  -- Check local norm bound
  match NormOp.checkLocal cfg share.z_i with
  | .exceeded actual bound =>
      .error (.normExceeded share.sender actual bound)
  | .ok =>
      -- Verify algebraic relation: A(z_i) = w_eff + c·pk_i
      -- where w_eff = hiding + ρ·binding
      let w_eff := commitment.hidingVal + bindingFactor • commitment.bindingVal
      let expected := w_eff + challenge • pkShare
      if S.A share.z_i = expected then
        .ok ()
      else
        .error (.algebraicInvalid share.sender "A(z_i) ≠ w_eff + c·pk_i")

/-- Validate share with norm check only (no algebraic check).
    Faster, but doesn't detect malformed shares. -/
def validateShareNormOnly [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (share : SignShareMsg S)
    : Except (ShareValidationError S.PartyId) Unit :=
  match NormOp.checkLocal cfg share.z_i with
  | .exceeded actual bound =>
      .error (.normExceeded share.sender actual bound)
  | .ok =>
      .ok ()

/-- Validate a batch of shares, collecting all errors. -/
def validateAll [NormBounded S.Secret] [DecidableEq S.Public]
    [BEq S.PartyId] [Hashable S.PartyId]
    [AddCommGroup S.Public] [Module S.Scalar S.Public]
    [SMul S.Challenge S.Public]
    (cfg : ThresholdConfig)
    (shares : List (SignShareMsg S))
    (commitments : List (SignCommitMsg S))
    (pkShares : S.PartyId → S.Public)
    (challenge : S.Challenge)
    (bindingFactors : BindingFactors S)
    : List (SignShareMsg S × Option (ShareValidationError S.PartyId)) :=
  shares.map fun share =>
    -- Find commitment for this share
    match commitments.find? (fun c => c.sender == share.sender) with
    | none =>
        (share, some (.missingCommitment share.sender))
    | some commit =>
        -- Find binding factor for this share
        match bindingFactors.get share.sender with
        | none =>
            (share, some (.missingBindingFactor share.sender))
        | some rho =>
            match validateShare cfg share commit (pkShares share.sender) challenge rho with
            | .ok () => (share, none)
            | .error e => (share, some e)

end ValidationOp

/-!
## Aggregation Result
-/

/-- Result of validated aggregation with blame information. -/
structure AggregationResult (S : Scheme) where
  /-- The aggregated signature (if successful) -/
  signature : Option (Signature S)
  /-- Valid shares that were included -/
  includedParties : List S.PartyId
  /-- Blame result from error collection -/
  blame : BlameResult S.PartyId
  /-- Whether we had enough valid shares -/
  success : Bool
  /-- Total shares received -/
  totalReceived : Nat
  /-- Valid shares count -/
  validCount : Nat

/-- Aggregation error when we don't have enough valid shares. -/
inductive AggregationError (PartyId : Type*)
  | insufficientShares (valid : Nat) (required : Nat)
  | noValidShares
  deriving Repr

/-- ToString for AggregationError -/
instance {PartyId : Type*} : ToString (AggregationError PartyId) where
  toString
    | .insufficientShares v r => s!"insufficient valid shares: {v} < {r} required"
    | .noValidShares => "no valid shares received"

/-!
## Validated Aggregation
-/

/-- Aggregate with per-share validation.

    This is the key aggregation function for local rejection:
    1. Validate each share against local bound
    2. Reject invalid shares (don't trigger global restart)
    3. Collect blame according to ProtocolConfig
    4. Aggregate first T valid shares
    5. Guarantee: aggregate satisfies global bound (by construction)

    Given sufficient honest parties (≥ threshold), always succeeds in one round.

    **Inputs**:
    - `cfg`: Threshold configuration
    - `protocolCfg`: Protocol configuration (controls blame collection)
    - `challenge`: Fiat-Shamir challenge
    - `commitments`: Round 1 commitment messages
    - `shares`: Round 2 share messages
    - `pkShares`: Function to look up public key shares
    - `bindingFactors`: Binding factors for all signers

    **Returns**: Aggregation result with signature or error info. -/
def aggregateValidated (S : Scheme)
    [NormBounded S.Secret] [DecidableEq S.Public]
    [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    [AddCommGroup S.Secret] [AddCommGroup S.Public]
    [Module S.Scalar S.Public]
    [SMul S.Challenge S.Public]
    (cfg : ThresholdConfig)
    (protocolCfg : ProtocolConfig)
    (challenge : S.Challenge)
    (commitments : List (SignCommitMsg S))
    (shares : List (SignShareMsg S))
    (pkShares : S.PartyId → S.Public)
    (bindingFactors : BindingFactors S)
    : AggregationResult S :=
  -- Validate all shares
  let results := ValidationOp.validateAll cfg shares commitments pkShares challenge bindingFactors

  -- Partition into valid and invalid
  let validShares := results.filter (fun (_, err) => err.isNone) |>.map Prod.fst
  let errors := results.filterMap fun (_, err) => err

  -- Collect blame according to config
  let blameResult := collectBlameWithLimit protocolCfg errors

  -- Check if we have enough valid shares
  if validShares.length < cfg.threshold then
    { signature := none
      includedParties := validShares.map (·.sender)
      blame := blameResult
      success := false
      totalReceived := shares.length
      validCount := validShares.length }
  else
    -- Take exactly threshold valid shares
    let toAggregate := validShares.take cfg.threshold

    -- Aggregate: z = Σ z_i
    let z := toAggregate.map (·.z_i) |>.foldl (· + ·) 0

    -- Build signature
    let sig : Signature S :=
      { c := challenge
        z := z
        Sset := toAggregate.map (·.sender)
        commits := [] }

    { signature := some sig
      includedParties := toAggregate.map (·.sender)
      blame := blameResult
      success := true
      totalReceived := shares.length
      validCount := validShares.length }

/-- Simple aggregation without validation (for comparison/testing).
    Use `aggregateValidated` in production. -/
def aggregateSimple (S : Scheme)
    [AddCommGroup S.Secret]
    (challenge : S.Challenge)
    (shares : List (SignShareMsg S))
    : Signature S :=
  let z := shares.map (·.z_i) |>.foldl (· + ·) 0
  { c := challenge, z := z, Sset := shares.map (·.sender), commits := [] }

/-!
## Verification Integration
-/

/-- Verify that aggregated signature satisfies global bound.
    This should always pass for properly validated aggregation. -/
def verifyAggregateBound (S : Scheme) [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (sig : Signature S)
    : NormCheckResult :=
  NormOp.checkGlobal cfg sig.z

/-- Full verification: global bound + algebraic check.

    **Inputs**:
    - `cfg`: Threshold configuration
    - `sig`: Aggregated signature
    - `pk`: Group public key
    - `aggregateW`: Aggregate nonce commitment

    **Checks**:
    1. ‖z‖∞ ≤ globalBound
    2. A(z) = w + c · pk -/
def verifySignature (S : Scheme) [NormBounded S.Secret] [DecidableEq S.Public]
    [AddCommGroup S.Public] [SMul S.Challenge S.Public]
    (cfg : ThresholdConfig)
    (sig : Signature S)
    (pk : S.Public)
    (aggregateW : S.Public)
    : Bool :=
  -- Check global norm bound
  match verifyAggregateBound S cfg sig with
  | .exceeded _ _ => false
  | .ok =>
      -- Check algebraic relation
      S.A sig.z = aggregateW + sig.c • pk

end IceNine.Protocol.ValidatedAggregation
