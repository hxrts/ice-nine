/-
# Session Abort Infrastructure

Provides abort coordination for session-level failures that cannot be
handled locally. Unlike local rejection (which handles norm bounds within
a single signer), aborts require distributed consensus to abandon a session.

## When Aborts Are Needed

1. **Liveness failures**: Parties offline, session times out
2. **Trust assumption violation**: More than n-t parties faulty
3. **DKG/VSS failures**: Too many complaints to continue
4. **Explicit cancellation**: Group decides to abandon signing

## Design Principles

- Uses `ThresholdConfig.abortThreshold` (f+1) for consensus
- Security violations trigger immediate abort (no voting)
- CRDT-mergeable state for distributed coordination
- Harmonized with `LocalRejectionError` and `ShareValidationError`

## Relationship to Local Rejection

Local rejection handles norm bounds *within* a signing attempt—each party
independently retries until finding a valid response. Aborts handle
*session-level* failures that require coordination to resolve.

| Mechanism | Scope | Coordination | Example |
|-----------|-------|--------------|---------|
| Local rejection | Single party | None | Norm bound exceeded |
| Abort | Session-wide | f+1 votes | Timeout, trust violation |
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.Core.CRDT
import IceNine.Protocol.Core.ThresholdConfig

set_option autoImplicit false

namespace IceNine.Protocol.Abort

open IceNine.Protocol
open IceNine.Protocol.ThresholdConfig

/-!
## Abort Reasons

Categorized by whether they require voting or trigger immediate abort.
-/

/-- Reasons a session may need to abort.

    **Liveness reasons** require f+1 votes to confirm abort:
    - `timeout`: Session timed out with insufficient responses
    - `insufficientParticipants`: Fewer than threshold parties participated
    - `partyUnresponsive`: Specific parties detected as unresponsive

    **Security violations** trigger immediate abort (no voting):
    - `trustViolation`: More than n-t parties are faulty
    - `globalNormExceeded`: Aggregate signature exceeds bound despite local rejection
    - `tooManyComplaints`: DKG/VSS had too many complaints to continue

    **Explicit abort** requires f+1 votes:
    - `requestedBy`: A party explicitly requested abort -/
inductive AbortReason (PartyId : Type*) where
  -- Liveness failures (require voting)
  | timeout (respondents : Nat) (required : Nat)
  | insufficientParticipants (actual : Nat) (required : Nat)
  | partyUnresponsive (parties : List PartyId)

  -- Security violations (immediate abort)
  | trustViolation (faultyCount : Nat) (maxTolerable : Nat)
  | globalNormExceeded (aggregateNorm : Nat) (bound : Nat)
  | tooManyComplaints (complaints : Nat) (maxTolerable : Nat)

  -- Explicit request (requires voting)
  | requestedBy (requester : PartyId)
  deriving DecidableEq, Repr

/-- Whether this reason triggers immediate abort without voting.

    Security violations are immediate because:
    1. They indicate the protocol cannot safely continue
    2. Waiting for votes could allow further damage
    3. Any honest party detecting the violation should halt -/
def AbortReason.isImmediate {PartyId : Type*} : AbortReason PartyId → Bool
  | .trustViolation _ _ => true
  | .globalNormExceeded _ _ => true
  | .tooManyComplaints _ _ => true
  | _ => false

/-- Whether this reason indicates a security violation (vs liveness). -/
def AbortReason.isSecurityViolation {PartyId : Type*} : AbortReason PartyId → Bool
  | .trustViolation _ _ => true
  | .globalNormExceeded _ _ => true
  | .tooManyComplaints _ _ => true
  | _ => false

/-- Whether this reason is blame-attributable. -/
def AbortReason.isBlameable {PartyId : Type*} : AbortReason PartyId → Bool
  | .partyUnresponsive ps => !ps.isEmpty
  | .requestedBy _ => true
  | _ => false

/-- Get blamed parties from an abort reason, if any. -/
def AbortReason.blamedParties {PartyId : Type*} : AbortReason PartyId → List PartyId
  | .partyUnresponsive ps => ps
  | .requestedBy p => [p]  -- Requester is "blamed" for the abort
  | _ => []

/-!
## Abort Messages
-/

/-- Abort proposal message sent by a party.

    When a party detects a condition requiring abort, it broadcasts
    this message to propose aborting the session. -/
structure AbortMsg (S : Scheme) where
  /-- Who is proposing the abort -/
  sender : S.PartyId
  /-- Which session to abort -/
  session : Nat
  /-- Why abort is requested -/
  reason : AbortReason S.PartyId
  /-- Evidence (e.g., list of unresponsive parties) -/
  evidence : List S.PartyId := []
  deriving Repr

/-- Create an abort message for timeout. -/
def AbortMsg.timeout (S : Scheme) (sender : S.PartyId) (session : Nat)
    (respondents required : Nat) : AbortMsg S :=
  { sender, session, reason := .timeout respondents required }

/-- Create an abort message for unresponsive parties. -/
def AbortMsg.unresponsive (S : Scheme) (sender : S.PartyId) (session : Nat)
    (unresponsive : List S.PartyId) : AbortMsg S :=
  { sender, session, reason := .partyUnresponsive unresponsive, evidence := unresponsive }

/-- Create an abort message for trust violation. -/
def AbortMsg.trustViolation (S : Scheme) (sender : S.PartyId) (session : Nat)
    (faultyCount maxTolerable : Nat) : AbortMsg S :=
  { sender, session, reason := .trustViolation faultyCount maxTolerable }

/-- Create an abort message for explicit request. -/
def AbortMsg.request (S : Scheme) (sender : S.PartyId) (session : Nat) : AbortMsg S :=
  { sender, session, reason := .requestedBy sender }

/-!
## Abort State (CRDT)

Abort state is CRDT-mergeable, allowing distributed coordination
even with message reordering and duplication.
-/

/-- Abort voting state for a session.

    This structure tracks:
    - Which parties have voted to abort
    - What reasons have been given
    - Whether an immediate abort was triggered

    **CRDT property**: Merging two states produces a state that
    reflects all votes and reasons from both. -/
structure AbortState (S : Scheme) where
  /-- Session being considered for abort -/
  session : Nat
  /-- Parties who have voted to abort -/
  votes : Finset S.PartyId
  /-- All reasons given (for diagnostics/logging) -/
  reasons : List (AbortReason S.PartyId)
  /-- Whether an immediate abort was triggered -/
  immediateTriggered : Bool := false
  deriving Repr

/-- Empty abort state for a session. -/
def AbortState.empty (S : Scheme) (session : Nat) : AbortState S :=
  { session, votes := ∅, reasons := [], immediateTriggered := false }

/-- Create abort state from a single message. -/
def AbortState.fromMsg {S : Scheme} (msg : AbortMsg S) : AbortState S :=
  { session := msg.session
    votes := {msg.sender}
    reasons := [msg.reason]
    immediateTriggered := msg.reason.isImmediate }

/-- CRDT merge for abort state.

    Union of votes, concatenation of reasons, OR of immediate flag. -/
instance (S : Scheme) [DecidableEq S.PartyId] : Join (AbortState S) :=
  ⟨fun a b => {
    session := a.session  -- Assume matching sessions
    votes := a.votes ∪ b.votes
    reasons := (a.reasons ++ b.reasons).dedup
    immediateTriggered := a.immediateTriggered || b.immediateTriggered
  }⟩

/-- Check if abort is confirmed by voting threshold.

    Requires at least `cfg.abortThreshold` (f+1) votes. -/
def AbortState.isConfirmedByVotes {S : Scheme}
    (state : AbortState S) (cfg : ThresholdConfig) : Bool :=
  state.votes.card ≥ cfg.abortThreshold

/-- Check if any reason triggered immediate abort. -/
def AbortState.hasImmediateReason {S : Scheme} (state : AbortState S) : Bool :=
  state.immediateTriggered || state.reasons.any AbortReason.isImmediate

/-- Should this session abort?

    A session aborts if either:
    1. An immediate abort was triggered (security violation), OR
    2. At least f+1 parties voted to abort -/
def AbortState.shouldAbort {S : Scheme}
    (state : AbortState S) (cfg : ThresholdConfig) : Bool :=
  state.hasImmediateReason || state.isConfirmedByVotes cfg

/-- Get all security-related reasons. -/
def AbortState.securityReasons {S : Scheme} (state : AbortState S)
    : List (AbortReason S.PartyId) :=
  state.reasons.filter AbortReason.isSecurityViolation

/-- Get all liveness-related reasons. -/
def AbortState.livenessReasons {S : Scheme} (state : AbortState S)
    : List (AbortReason S.PartyId) :=
  state.reasons.filter (fun r => !r.isSecurityViolation)

/-- Number of votes received. -/
def AbortState.voteCount {S : Scheme} (state : AbortState S) : Nat :=
  state.votes.card

/-- Process an incoming abort message, updating state. -/
def AbortState.processMsg {S : Scheme} [DecidableEq S.PartyId]
    (state : AbortState S) (msg : AbortMsg S) : AbortState S :=
  if msg.session = state.session then
    Join.join state (AbortState.fromMsg msg)
  else
    state  -- Ignore messages for different sessions

/-!
## Abort Result

Unified result type for operations that may abort.
-/

/-- Outcome of an operation that may abort.

    This harmonizes with `LocalSignResult` and `ShareValidationError`:
    - `success`: Operation completed successfully
    - `aborted`: Session was aborted with reason -/
inductive AbortResult (S : Scheme) (A : Type*) where
  | success (value : A)
  | aborted (reason : AbortReason S.PartyId) (votes : Nat)
  deriving Repr

/-- Check if result is success. -/
def AbortResult.isSuccess {S : Scheme} {A : Type*} : AbortResult S A → Bool
  | .success _ => true
  | .aborted _ _ => false

/-- Get value from successful result. -/
def AbortResult.getValue {S : Scheme} {A : Type*} : AbortResult S A → Option A
  | .success v => some v
  | .aborted _ _ => none

/-- Map over successful results. -/
def AbortResult.map {S : Scheme} {A B : Type*}
    (f : A → B) : AbortResult S A → AbortResult S B
  | .success v => .success (f v)
  | .aborted r n => .aborted r n

/-- Convert to Except. -/
def AbortResult.toExcept {S : Scheme} {A : Type*}
    : AbortResult S A → Except (AbortReason S.PartyId × Nat) A
  | .success v => .ok v
  | .aborted r n => .error (r, n)

/-!
## ToString Instances
-/

/-- ToString for AbortReason -/
instance {PartyId : Type*} [ToString PartyId] : ToString (AbortReason PartyId) where
  toString
    | .timeout resp req => s!"timeout: {resp}/{req} responded"
    | .insufficientParticipants actual req =>
        s!"insufficient participants: {actual}/{req}"
    | .partyUnresponsive ps => s!"unresponsive parties: {ps}"
    | .trustViolation faulty max =>
        s!"trust violation: {faulty} faulty (max {max})"
    | .globalNormExceeded norm bound =>
        s!"global norm exceeded: {norm} > {bound}"
    | .tooManyComplaints complaints max =>
        s!"too many complaints: {complaints} (max {max})"
    | .requestedBy p => s!"requested by {p}"

/-- ToString for AbortMsg -/
instance {S : Scheme} [ToString S.PartyId] : ToString (AbortMsg S) where
  toString msg :=
    s!"AbortMsg(session={msg.session}, sender={msg.sender}, reason={msg.reason})"

/-- ToString for AbortState -/
instance {S : Scheme} [ToString S.PartyId] : ToString (AbortState S) where
  toString state :=
    let immediate := if state.immediateTriggered then " [IMMEDIATE]" else ""
    s!"AbortState(session={state.session}, votes={state.votes.card}, " ++
    s!"reasons={state.reasons.length}{immediate})"

end IceNine.Protocol.Abort
