/-
# Error Handling Patterns

Unified documentation and utilities for error types across the protocol.
Each module defines domain-specific error types; this module provides
the common patterns and re-exports for convenience.

## Design Philosophy

Error types in Ice Nine follow these principles:

1. **Domain-specific types**: Each module defines errors relevant to its operations
2. **Blame attribution**: Errors carry party IDs to identify misbehavior
3. **Recoverable vs fatal**: Some errors allow continuation (complaints), others abort
4. **Result types**: Use `Except` for operations that can fail

## Error Categories

| Module | Type | Category | Description |
|--------|------|----------|-------------|
| DKGCore | `DkgError` | Fatal | Protocol abort required |
| DKGThreshold | `Complaint` | Recoverable | Party exclusion possible |
| DKGThreshold | `ExclusionResult` | Result | Quorum check outcome |
| VSS | `VSSError` | Fatal/Recoverable | Depends on complaint count |
| RefreshCoord | `CommitValidationError` | Validation | Commit validation outcome |
| RefreshCoord | `RevealValidationError` | Validation | Reveal validation outcome |
| RepairCoord | `ContribCommitValidationError` | Validation | Commit validation outcome |
| RepairCoord | `ContribRevealValidationError` | Validation | Reveal validation outcome |
-/

import IceNine.Protocol.DKG.Core
import IceNine.Protocol.DKG.Threshold
import IceNine.Protocol.DKG.VSS
import IceNine.Protocol.Shares.RefreshCoord
import IceNine.Protocol.Shares.RepairCoord

namespace IceNine.Protocol.Error

open IceNine.Protocol

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
## Error Display

String conversion for logging/debugging.
-/

/-- Display DkgError -/
def showDkgError {PartyId : Type*} [ToString PartyId] : DkgError PartyId → String
  | .lengthMismatch => "DKG Error: commits/reveals count mismatch"
  | .duplicatePids => "DKG Error: duplicate party IDs"
  | .commitMismatch p => s!"DKG Error: commitment mismatch for party {p}"
  | .invalidProofOfKnowledge p => s!"DKG Error: invalid proof of knowledge from party {p}"

/-- Display Complaint -/
def showComplaint {PartyId : Type*} [ToString PartyId] : Complaint PartyId → String
  | .openingMismatch p => s!"Complaint: opening mismatch by {p}"
  | .missingReveal p => s!"Complaint: missing reveal from {p}"

/-- Display VSSError -/
def showVSSError {PartyId : Type*} [ToString PartyId] : VSS.VSSError PartyId → String
  | .shareVerificationFailed accused complainant =>
      s!"VSS Error: share from {accused} failed verification (reported by {complainant})"
  | .missingCommitment p => s!"VSS Error: missing commitment from {p}"
  | .missingShare sender recipient => s!"VSS Error: missing share from {sender} to {recipient}"
  | .thresholdMismatch expected got =>
      s!"VSS Error: threshold mismatch (expected {expected}, got {got})"
  | .duplicateDealer p => s!"VSS Error: duplicate dealer {p}"

end IceNine.Protocol.Error
