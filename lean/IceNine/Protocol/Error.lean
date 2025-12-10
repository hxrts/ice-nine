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
| RepairCoord | `ContribCommitResult` | Result | Commit processing outcome |
| RepairCoord | `ContribRevealResult` | Result | Reveal processing outcome |
-/

import IceNine.Protocol.DKGCore
import IceNine.Protocol.DKGThreshold
import IceNine.Protocol.VSS
import IceNine.Protocol.RepairCoord

namespace IceNine.Protocol.Error

open IceNine.Protocol

/-!
## Common Error Interface

Type class for errors that identify a faulty party.
-/

/-- Errors that can identify a misbehaving party. -/
class BlameableError (E : Type*) (PartyId : Type*) where
  /-- Get the party responsible for this error, if identifiable -/
  blamedParty : E → Option PartyId

/-- DkgError is blameable for commitMismatch -/
instance {PartyId : Type*} : BlameableError (DkgError PartyId) PartyId where
  blamedParty
    | .lengthMismatch => none
    | .duplicatePids => none
    | .commitMismatch p => some p

/-- Complaint always identifies the accused party -/
instance {PartyId : Type*} : BlameableError (Complaint PartyId) PartyId where
  blamedParty c := some c.accused

/-- VSSError is blameable for most variants -/
instance {PartyId : Type*} : BlameableError (VSS.VSSError PartyId) PartyId where
  blamedParty
    | .shareVerificationFailed accused _ => some accused
    | .missingCommitment p => some p
    | .missingShare from _ => some from
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

/-- Get all unique blamed parties from a list of errors -/
def allBlamedParties {E PartyId : Type*} [DecidableEq PartyId] [BlameableError E PartyId]
    (errors : List E) : List PartyId :=
  (errors.filterMap BlameableError.blamedParty).dedup

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

/-- Display Complaint -/
def showComplaint {PartyId : Type*} [ToString PartyId] : Complaint PartyId → String
  | .openingMismatch p => s!"Complaint: opening mismatch by {p}"
  | .missingReveal p => s!"Complaint: missing reveal from {p}"

/-- Display VSSError -/
def showVSSError {PartyId : Type*} [ToString PartyId] : VSS.VSSError PartyId → String
  | .shareVerificationFailed accused complainant =>
      s!"VSS Error: share from {accused} failed verification (reported by {complainant})"
  | .missingCommitment p => s!"VSS Error: missing commitment from {p}"
  | .missingShare from to => s!"VSS Error: missing share from {from} to {to}"
  | .thresholdMismatch expected got =>
      s!"VSS Error: threshold mismatch (expected {expected}, got {got})"
  | .duplicateDealer p => s!"VSS Error: duplicate dealer {p}"

end IceNine.Protocol.Error
