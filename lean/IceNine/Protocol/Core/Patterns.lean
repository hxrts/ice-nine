/-
# Reusable Protocol Patterns

This module contains Scheme-independent reusable abstractions:
- Constraint aliases for cleaner function signatures (generic versions)
- Commit-reveal protocol framework
- Utility functions

Scheme-specific constraint aliases (PartyIdHash, etc.) are in Core.lean.

These patterns reduce code duplication and ensure consistency across
DKG, refresh, repair, and signing protocols.
-/

import Mathlib

namespace IceNine.Protocol

/-!
## Standard Constraint Aliases

These abbreviations reduce verbosity in function signatures. The Protocol modules
frequently require the same combinations of type class constraints on party IDs.

**Usage**: Replace verbose constraint lists with these aliases:
```lean
-- Before:
def foo (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] ...

-- After:
def foo (S : Scheme) [PartyIdHash S] [DecidableEq S.PartyId] ...
```

**Note**: These are defined as product types so they can bundle multiple constraints.
-/

/-- Constraints for HashMap-keyed structures (MsgMap, NonceRegistry).
    Provides boolean equality and hashing for party IDs. -/
abbrev HashConstraints (PartyId : Type*) := BEq PartyId × Hashable PartyId

/-- Extract BEq instance from HashConstraints. -/
def HashConstraints.toBEq {PartyId : Type*} (h : HashConstraints PartyId) : BEq PartyId := h.1

/-- Extract Hashable instance from HashConstraints. -/
def HashConstraints.toHashable {PartyId : Type*} (h : HashConstraints PartyId) : Hashable PartyId := h.2

/-- Full constraints for state operations: HashMap + decidable equality.
    Use when functions need both HashMap operations and if-then-else guards. -/
abbrev StateConstraints (PartyId : Type*) := HashConstraints PartyId × DecidableEq PartyId

/-- Extract HashConstraints from StateConstraints. -/
def StateConstraints.toHash {PartyId : Type*} (h : StateConstraints PartyId) : HashConstraints PartyId := h.1

/-- Extract DecidableEq from StateConstraints. -/
def StateConstraints.toDecidableEq {PartyId : Type*} (h : StateConstraints PartyId) : DecidableEq PartyId := h.2

/-- Constraints for Lagrange coefficient computation.
    Requires field arithmetic and decidable equality on scalars. -/
abbrev FieldConstraints (Scalar : Type*) := Field Scalar × DecidableEq Scalar

/-- Extract Field instance from FieldConstraints. -/
def FieldConstraints.toField {Scalar : Type*} (h : FieldConstraints Scalar) : Field Scalar := h.1

/-- Extract DecidableEq instance from FieldConstraints. -/
def FieldConstraints.toDecidableEq {Scalar : Type*} (h : FieldConstraints Scalar) : DecidableEq Scalar := h.2

/-!
## Commit-Reveal Protocol Framework

The commit-reveal pattern appears in DKG, refresh, and repair protocols.
Each follows the same structure:
1. Party creates local state and commit message
2. Party broadcasts commit
3. After all commits received, party reveals
4. Reveals are verified against commits

This framework provides reusable components for this pattern.
-/

/-- Generic validation error for commit-reveal protocols.
    Parameterized by phase type and party ID type for flexibility. -/
inductive CommitRevealError (PhaseType PartyId : Type*)
  | wrongPhase (current : PhaseType)
  | senderNotAuthorized (sender : PartyId)
  | duplicateMessage (sender : PartyId)
  | commitmentMismatch (sender : PartyId)
  | missingCommit (sender : PartyId)
  | verificationFailed (sender : PartyId) (reason : String)
  deriving Repr

/-- Result of processing a commit message. -/
inductive CommitResult (PartyId : Type*)
  | accepted
  | duplicate (sender : PartyId)
  | notAuthorized (sender : PartyId)
  deriving Repr, DecidableEq

/-- Result of processing a reveal message. -/
inductive RevealResult (PartyId : Type*)
  | accepted
  | duplicate (sender : PartyId)
  | noMatchingCommit (sender : PartyId)
  | verificationFailed (sender : PartyId)
  deriving Repr, DecidableEq

/-- Typeclass for messages with a sender field.
    Enables generic sender extraction in commit-reveal processing. -/
class HasSender (M : Type*) (PartyId : Type*) where
  sender : M → PartyId

/-- Extract sender from any message type with HasSender instance. -/
def getSender {M PartyId : Type*} [HasSender M PartyId] (m : M) : PartyId :=
  HasSender.sender m

/-- Generic function to check if a party is authorized for a protocol.
    Used to filter commits/reveals from non-participants. -/
def isAuthorized {PartyId : Type*} [DecidableEq PartyId]
    (authorizedParties : List PartyId) (party : PartyId) : Bool :=
  authorizedParties.contains party

/-- Extract unique party IDs from a list using a key function.
    Useful for deduplicating message senders, complaint targets, etc.

    **Usage**:
    - `extractUnique (·.sender) messages` - get unique senders
    - `extractUnique (·.accused) complaints` - get unique accused parties -/
def extractUnique {α β : Type*} [DecidableEq β] (key : α → β) (items : List α) : List β :=
  (items.map key).dedup

end IceNine.Protocol
