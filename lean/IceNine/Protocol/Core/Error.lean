/-
# Error Handling Patterns

Unified error infrastructure for the Ice Nine protocol. This module provides:

1. **BlameableError typeclass**: Identifies misbehaving parties for accountability
2. **ToString instances**: Unified logging for all protocol error types
3. **Error aggregation**: Utilities for collecting and categorizing errors
4. **Result conversion**: Helpers for Except/Option interop
5. **Generic validation errors**: Unified commit/reveal validation across protocols

## Design Philosophy

Error types in Ice Nine follow these principles:

1. **Domain-specific types**: Each module defines errors relevant to its operations
2. **Blame attribution**: Errors carry party IDs to identify misbehavior
3. **Recoverable vs fatal**: Some errors allow continuation (complaints), others abort
4. **Result types**: Use `Except` for operations that can fail
5. **ToString consistency**: All errors have ToString instances for logging

## Error Categories

| Module | Type | Category | Blameable | Description |
|--------|------|----------|-----------|-------------|
| DKGCore | `DkgError` | Fatal | ✓ | Protocol abort required |
| DKGThreshold | `Complaint` | Recoverable | ✓ | Party exclusion possible |
| VSS | `VSSError` | Fatal/Recoverable | ✓ | Depends on complaint count |
| Dealer | `DealerError` | Fatal | - | Setup failed |
| Sign | `SignError` | Fatal | ✓ | Signing failed |
| Sign | `BindingError` | Fatal | ✓ | Binding validation failed |
| Sign | `LocalRejectionError` | Recoverable | ✓ | Local rejection exhausted |
| Sign | `ShareValidationError` | Recoverable | ✓ | Invalid partial signature |
| RefreshCoord | `CoordinatorError` | Fatal | - | Coordinator selection failed |
| RefreshDKG | `RefreshDKGError` | Fatal | ✓ | Refresh failed |
| Validation | `ValidationError` | Fatal | ✓ | Generic commit/reveal errors |
-/

import IceNine.Protocol.DKG.Core
import IceNine.Protocol.DKG.Dealer
import IceNine.Protocol.DKG.Threshold
import IceNine.Protocol.DKG.VSS
import IceNine.Protocol.Sign.Types
import IceNine.Protocol.Sign.Core
import IceNine.Protocol.Shares.RefreshCoord
import IceNine.Protocol.Shares.RepairCoord
import IceNine.Protocol.Shares.RefreshDKG

namespace IceNine.Protocol.Error

open IceNine.Protocol
open IceNine.Protocol.RefreshCoord
open IceNine.Protocol.RefreshDKG

/-!
## Cheater Detection Configuration

Following FROST, we provide configurable cheater detection modes.
Different deployments may prioritize performance vs. completeness.
-/

/-- Cheater detection mode determines how thoroughly we identify misbehaving parties.

    - `disabled`: No blame tracking (best performance, no accountability)
    - `firstCheater`: Stop at first identified cheater (good balance)
    - `allCheaters`: Exhaustively identify all cheaters (complete but slower) -/
inductive CheaterDetectionMode
  | disabled      -- No blame tracking
  | firstCheater  -- Stop after finding one cheater
  | allCheaters   -- Find all cheaters
  deriving DecidableEq, Repr

/-- Protocol configuration for error handling. -/
structure ProtocolConfig where
  /-- How thoroughly to identify cheaters -/
  cheaterDetection : CheaterDetectionMode := .firstCheater
  /-- Maximum errors to collect before aborting (0 = unlimited) -/
  maxErrors : Nat := 0
  deriving Repr

/-- Default protocol configuration. -/
def ProtocolConfig.default : ProtocolConfig :=
  { cheaterDetection := .firstCheater, maxErrors := 0 }

/-- High-security configuration: find all cheaters. -/
def ProtocolConfig.highSecurity : ProtocolConfig :=
  { cheaterDetection := .allCheaters, maxErrors := 0 }

/-- Performance configuration: no blame tracking. -/
def ProtocolConfig.performance : ProtocolConfig :=
  { cheaterDetection := .disabled, maxErrors := 1 }

/-!
## Common Error Interface

Type class for errors that identify a faulty party.
-/

/-- Errors that can identify a misbehaving party. -/
class BlameableError (E : Type*) (PartyId : Type*) where
  /-- Get the party responsible for this error, if identifiable -/
  blamedParty : E → Option PartyId

/-- DkgError is blameable for commitMismatch and invalidProofOfKnowledge -/
instance {PartyId : Type*} : BlameableError (DkgError PartyId) PartyId where
  blamedParty
    | .lengthMismatch => none
    | .duplicatePids => none
    | .commitMismatch p => some p
    | .invalidProofOfKnowledge p => some p

/-- Complaint always identifies the accused party -/
instance {PartyId : Type*} : BlameableError (Complaint PartyId) PartyId where
  blamedParty c := some c.accused

/-- VSSError is blameable for most variants -/
instance {PartyId : Type*} : BlameableError (VSS.VSSError PartyId) PartyId where
  blamedParty
    | .shareVerificationFailed accused _ => some accused
    | .missingCommitment p => some p
    | .missingShare sender _ => some sender
    | .thresholdMismatch _ _ => none
    | .duplicateDealer p => some p

/-!
## Error Aggregation

Utilities for collecting and categorizing multiple errors.
-/

/-- Count how many errors blame a specific party -/
def countBlame {E PartyId : Type*} [DecidableEq PartyId] [BlameableError E PartyId]
    (errors : List E) (party : PartyId) : Nat :=
  errors.countP fun e =>
    match BlameableError.blamedParty e with
    | some p => p = party
    | none => false

/-- Get all unique blamed parties from a list of errors.
    Note: Uses filterMap then dedup since BlameableError.blamedParty returns Option. -/
def allBlamedParties {E PartyId : Type*} [DecidableEq PartyId] [BlameableError E PartyId]
    (errors : List E) : List PartyId :=
  (errors.filterMap BlameableError.blamedParty).dedup

/-- Result of blame collection respecting detection mode. -/
structure BlameResult (PartyId : Type*) where
  /-- Identified cheaters (may be partial based on mode) -/
  cheaters : List PartyId
  /-- Whether collection was exhaustive -/
  isComplete : Bool
  /-- Number of errors processed -/
  errorsProcessed : Nat
  deriving Repr

/-- Collect blame from errors respecting the detection mode.
    Returns early for `firstCheater` mode, exhaustively for `allCheaters`. -/
def collectBlame {E PartyId : Type*} [DecidableEq PartyId] [BlameableError E PartyId]
    (config : ProtocolConfig) (errors : List E) : BlameResult PartyId :=
  match config.cheaterDetection with
  | .disabled =>
      { cheaters := [], isComplete := true, errorsProcessed := 0 }
  | .firstCheater =>
      -- Find first blamed party and stop
      match errors.findSome? BlameableError.blamedParty with
      | some p => { cheaters := [p], isComplete := false, errorsProcessed := 1 }
      | none => { cheaters := [], isComplete := true, errorsProcessed := errors.length }
  | .allCheaters =>
      -- Exhaustively collect all blamed parties
      let cheaters := allBlamedParties errors
      { cheaters := cheaters, isComplete := true, errorsProcessed := errors.length }

/-- Collect blame with early termination based on maxErrors. -/
def collectBlameWithLimit {E PartyId : Type*} [DecidableEq PartyId] [BlameableError E PartyId]
    (config : ProtocolConfig) (errors : List E) : BlameResult PartyId :=
  let limitedErrors :=
    if config.maxErrors > 0 then errors.take config.maxErrors
    else errors
  let result := collectBlame config limitedErrors
  { result with isComplete := result.isComplete && (config.maxErrors = 0 || errors.length ≤ config.maxErrors) }

/-- Check if we should continue collecting errors based on config. -/
def shouldContinueCollecting {PartyId : Type*} (config : ProtocolConfig) (result : BlameResult PartyId) : Bool :=
  match config.cheaterDetection with
  | .disabled => false
  | .firstCheater => result.cheaters.isEmpty
  | .allCheaters =>
      config.maxErrors = 0 || result.errorsProcessed < config.maxErrors

/-!
## Result Conversion

Utilities for converting between different result types.
-/

/-- Convert Except to Option, discarding error info -/
def exceptToOption {E A : Type*} : Except E A → Option A
  | .ok a => some a
  | .error _ => none

/-- Convert Option to Except with default error -/
def optionToExcept {E A : Type*} (defaultErr : E) : Option A → Except E A
  | some a => .ok a
  | none => .error defaultErr

/-!
## ToString Instances

Unified string conversion for all protocol error types.
Wire show* helper functions to ToString typeclass instances.
-/

/-- Display DkgError -/
def showDkgError {PartyId : Type*} [ToString PartyId] : DkgError PartyId → String
  | .lengthMismatch => "DKG Error: commits/reveals count mismatch"
  | .duplicatePids => "DKG Error: duplicate party IDs"
  | .commitMismatch p => s!"DKG Error: commitment mismatch for party {p}"
  | .invalidProofOfKnowledge p => s!"DKG Error: invalid proof of knowledge from party {p}"

/-- ToString instance for DkgError -/
instance {PartyId : Type*} [ToString PartyId] : ToString (DkgError PartyId) :=
  ⟨showDkgError⟩

/-- Display Complaint -/
def showComplaint {PartyId : Type*} [ToString PartyId] : Complaint PartyId → String
  | .openingMismatch p => s!"Complaint: opening mismatch by {p}"
  | .missingReveal p => s!"Complaint: missing reveal from {p}"

/-- ToString instance for Complaint -/
instance {PartyId : Type*} [ToString PartyId] : ToString (Complaint PartyId) :=
  ⟨showComplaint⟩

/-- Display VSSError -/
def showVSSError {PartyId : Type*} [ToString PartyId] : VSS.VSSError PartyId → String
  | .shareVerificationFailed accused complainant =>
      s!"VSS Error: share from {accused} failed verification (reported by {complainant})"
  | .missingCommitment p => s!"VSS Error: missing commitment from {p}"
  | .missingShare sender recipient => s!"VSS Error: missing share from {sender} to {recipient}"
  | .thresholdMismatch expected got =>
      s!"VSS Error: threshold mismatch (expected {expected}, got {got})"
  | .duplicateDealer p => s!"VSS Error: duplicate dealer {p}"

/-- ToString instance for VSSError -/
instance {PartyId : Type*} [ToString PartyId] : ToString (VSS.VSSError PartyId) :=
  ⟨showVSSError⟩

/-- Display DealerError -/
def showDealerError : DealerError → String := DealerError.toString

/-- Display CoordinatorError -/
def showCoordinatorError : RefreshCoord.CoordinatorError → String :=
  RefreshCoord.CoordinatorError.toString

/-- Display SignError -/
def showSignError {PartyId : Type*} [ToString PartyId] : SignError PartyId → String
  | .lengthMismatch => "Sign Error: commits/reveals/shares count mismatch"
  | .participantMismatch p => s!"Sign Error: unexpected participant {p}"
  | .duplicateParticipants p => s!"Sign Error: duplicate participant {p}"
  | .commitMismatch p => s!"Sign Error: commitment mismatch for party {p}"
  | .sessionMismatch expected got =>
      s!"Sign Error: session mismatch (expected {expected}, got {got})"

/-- ToString instance for SignError -/
instance {PartyId : Type*} [ToString PartyId] : ToString (SignError PartyId) :=
  ⟨showSignError⟩

/-- Display BindingError -/
def showBindingError {PartyId : Type*} [ToString PartyId] : BindingError PartyId → String
  | .missingBindingFactor p => s!"Binding Error: missing binding factor for party {p}"
  | .bindingMismatch p => s!"Binding Error: binding mismatch for party {p}"
  | .contextMismatch => "Binding Error: context mismatch"

/-- ToString instance for BindingError -/
instance {PartyId : Type*} [ToString PartyId] : ToString (BindingError PartyId) :=
  ⟨showBindingError⟩

/-- Display RefreshDKGError -/
def showRefreshDKGError {PartyId : Type*} [ToString PartyId] : RefreshDKGError PartyId → String
  | .missingCommit p => s!"RefreshDKG Error: missing commitment from party {p}"
  | .missingShare from to => s!"RefreshDKG Error: missing share from {from} to {to}"
  | .invalidShare p => s!"RefreshDKG Error: invalid share from party {p}"
  | .thresholdMismatch expected got =>
      s!"RefreshDKG Error: threshold mismatch (expected {expected}, got {got})"

/-- ToString instance for RefreshDKGError -/
instance {PartyId : Type*} [ToString PartyId] : ToString (RefreshDKGError PartyId) :=
  ⟨showRefreshDKGError⟩

/-!
## Additional BlameableError Instances

Add blame attribution for SignError, BindingError, and RefreshDKGError.
-/

/-- SignError is blameable for participant-specific errors -/
instance {PartyId : Type*} : BlameableError (SignError PartyId) PartyId where
  blamedParty
    | .lengthMismatch => none
    | .participantMismatch p => some p
    | .duplicateParticipants p => some p
    | .commitMismatch p => some p
    | .sessionMismatch _ _ => none

/-- BindingError is blameable for party-specific errors -/
instance {PartyId : Type*} : BlameableError (BindingError PartyId) PartyId where
  blamedParty
    | .missingBindingFactor p => some p
    | .bindingMismatch p => some p
    | .contextMismatch => none

/-- RefreshDKGError is blameable for party-specific errors -/
instance {PartyId : Type*} : BlameableError (RefreshDKGError PartyId) PartyId where
  blamedParty
    | .missingCommit p => some p
    | .missingShare from _ => some from  -- blame sender
    | .invalidShare p => some p
    | .thresholdMismatch _ _ => none

/-!
## Local Rejection Errors

Error types for local rejection sampling in threshold signing.
-/

/-- Errors during local rejection sampling.

    These errors occur when a party cannot produce a valid partial signature
    within the configured attempt limit.

    **Blame**: The party ID is included for logging/diagnostics, but these
    errors don't necessarily indicate malicious behavior - they may occur
    due to unlucky randomness. -/
inductive LocalRejectionError (PartyId : Type*)
  | maxAttemptsExceeded (party : PartyId) (attempts : Nat) (localBound : Nat)
      -- Exhausted all local rejection attempts without finding valid z_i
  | invalidConfiguration (reason : String)
      -- ThresholdConfig is invalid (should not happen in normal use)
  deriving Repr

/-- BlameableError instance for LocalRejectionError.
    Note: maxAttemptsExceeded returns the party, but this is for diagnostics
    not blame - failing to find a valid z_i after many attempts is unlucky,
    not malicious. -/
instance {PartyId : Type*} : BlameableError (LocalRejectionError PartyId) PartyId where
  blamedParty
    | .maxAttemptsExceeded p _ _ => some p  -- For diagnostics, not blame
    | .invalidConfiguration _ => none

/-- ToString for LocalRejectionError -/
instance {PartyId : Type*} [ToString PartyId] : ToString (LocalRejectionError PartyId) where
  toString
    | .maxAttemptsExceeded p attempts bound =>
        s!"local rejection: party {p} exceeded {attempts} attempts (bound={bound})"
    | .invalidConfiguration reason =>
        s!"local rejection: invalid configuration - {reason}"

/-!
## Share Validation Errors

Errors during share validation in aggregation.
-/

/-- Errors during share validation at aggregation time.

    These errors indicate a party sent an invalid partial signature.
    Unlike LocalRejectionError, these DO indicate potential misbehavior
    and are used for blame attribution.

    **Blame**: All variants identify the misbehaving party. -/
inductive ShareValidationError (PartyId : Type*)
  | normExceeded (party : PartyId) (actualNorm : Nat) (localBound : Nat)
      -- Share's z_i exceeds local norm bound
  | algebraicInvalid (party : PartyId) (reason : String)
      -- Share fails algebraic verification: A(z_i) ≠ w_eff_i + c·pk_i
  | missingCommitment (party : PartyId)
      -- No commitment found for this party
  | missingBindingFactor (party : PartyId)
      -- No binding factor computed for this party
  deriving Repr

/-- BlameableError instance for ShareValidationError.
    All variants identify a potentially misbehaving party. -/
instance {PartyId : Type*} : BlameableError (ShareValidationError PartyId) PartyId where
  blamedParty
    | .normExceeded p _ _ => some p
    | .algebraicInvalid p _ => some p
    | .missingCommitment p => some p
    | .missingBindingFactor p => some p

/-- ToString for ShareValidationError -/
instance {PartyId : Type*} [ToString PartyId] : ToString (ShareValidationError PartyId) where
  toString
    | .normExceeded p actual bound =>
        s!"share from {p} exceeded local bound: {actual} > {bound}"
    | .algebraicInvalid p reason =>
        s!"share from {p} algebraically invalid: {reason}"
    | .missingCommitment p =>
        s!"missing commitment for {p}"
    | .missingBindingFactor p =>
        s!"missing binding factor for {p}"

/-!
## Generic Validation Errors

Unified validation error type for commit/reveal protocols.
Replaces duplicate types in RefreshCoord and RepairCoord.
-/

/-- Protocol phase for validation context -/
inductive ValidationPhase
  | commit
  | reveal
  deriving DecidableEq, Repr

/-- Generic validation error for commit/reveal protocols.
    Unifies `CommitValidationError`, `RevealValidationError`,
    `ContribCommitValidationError`, and `ContribRevealValidationError`. -/
inductive ValidationError (PartyId Phase : Type*)
  | wrongPhase (expected : Phase) (current : Phase)
      -- Operation attempted in wrong phase
  | notParticipant (sender : PartyId)
      -- Sender is not a valid participant
  | noCommit (sender : PartyId)
      -- Reveal without prior commit
  | invalidOpening (sender : PartyId)
      -- Commitment doesn't open correctly
  | conflict (sender : PartyId)
      -- Conflicting message from same sender
  deriving DecidableEq

/-- ToString instance for ValidationError -/
instance {PartyId Phase : Type*} [ToString PartyId] [ToString Phase]
    : ToString (ValidationError PartyId Phase) where
  toString
    | .wrongPhase exp cur => s!"Validation Error: wrong phase (expected {exp}, got {cur})"
    | .notParticipant p => s!"Validation Error: {p} is not a participant"
    | .noCommit p => s!"Validation Error: reveal without commit from {p}"
    | .invalidOpening p => s!"Validation Error: invalid opening from {p}"
    | .conflict p => s!"Validation Error: conflicting message from {p}"

/-- BlameableError instance for ValidationError -/
instance {PartyId Phase : Type*} : BlameableError (ValidationError PartyId Phase) PartyId where
  blamedParty
    | .wrongPhase _ _ => none
    | .notParticipant p => some p
    | .noCommit p => some p
    | .invalidOpening p => some p
    | .conflict p => some p

/-- Repr instance for ValidationError -/
instance {PartyId Phase : Type*} [Repr PartyId] [Repr Phase]
    : Repr (ValidationError PartyId Phase) where
  reprPrec e _ := match e with
    | .wrongPhase exp cur => s!"ValidationError.wrongPhase {repr exp} {repr cur}"
    | .notParticipant p => s!"ValidationError.notParticipant {repr p}"
    | .noCommit p => s!"ValidationError.noCommit {repr p}"
    | .invalidOpening p => s!"ValidationError.invalidOpening {repr p}"
    | .conflict p => s!"ValidationError.conflict {repr p}"

/-!
## Convenience Type Aliases

Specialized validation errors for common protocol phases.
-/

/-- Validation error for commit phase -/
abbrev CommitValidationErr (PartyId Phase : Type*) := ValidationError PartyId Phase

/-- Validation error for reveal phase -/
abbrev RevealValidationErr (PartyId Phase : Type*) := ValidationError PartyId Phase

/-!
## Error Conversion Utilities

Convert between domain-specific and generic validation errors.
These functions extract the sender from the conflicting message where available.
-/

/-- Convert RefreshCoord CommitValidationError to generic ValidationError.
    Extracts the sender from the existing message for conflict cases.
    Note: RefreshCoord.CommitValidationError has fewer cases than the generic type. -/
def fromRefreshCommitError {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (e : RefreshCoord.CommitValidationError S) : ValidationError S.PartyId RefreshPhase :=
  match e with
  | .wrongPhase p => .wrongPhase .commit p
  | .conflict existing => .conflict existing.sender

/-- Convert RefreshCoord RevealValidationError to generic ValidationError -/
def fromRefreshRevealError {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (e : RefreshCoord.RevealValidationError S) : ValidationError S.PartyId RefreshPhase :=
  match e with
  | .wrongPhase p => .wrongPhase .reveal p
  | .noCommit p => .noCommit p
  | .invalidOpening p => .invalidOpening p
  | .conflict existing => .conflict existing.sender

/-- Convert RepairCoord ContribCommitValidationError to generic ValidationError -/
def fromRepairCommitError {S : Scheme}
    (e : RepairCoord.ContribCommitValidationError S) : ValidationError S.PartyId RepairCoord.RepairPhase :=
  match e with
  | .wrongPhase p => .wrongPhase .commit p
  | .notHelper p => .notParticipant p
  | .conflict existing => .conflict existing.sender

/-- Convert RepairCoord ContribRevealValidationError to generic ValidationError -/
def fromRepairRevealError {S : Scheme}
    (e : RepairCoord.ContribRevealValidationError S) : ValidationError S.PartyId RepairCoord.RepairPhase :=
  match e with
  | .wrongPhase p => .wrongPhase .reveal p
  | .noCommit p => .noCommit p
  | .invalidOpening p => .invalidOpening p
  | .conflict existing => .conflict existing.sender

end IceNine.Protocol.Error
