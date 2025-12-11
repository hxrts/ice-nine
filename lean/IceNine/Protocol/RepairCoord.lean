/-
# Repair Coordination Protocol

Distributed protocol for coordinating share repair. The requester (party who
lost their share) coordinates with helpers to reconstruct their lost sk_i.

Protocol:
1. Requester broadcasts repair request with known pk_i
2. Helpers commit to their Lagrange-weighted contributions
3. Helpers reveal contributions after all commits received
4. Requester aggregates and verifies: A(sk_i) = pk_i

This provides:
- **Verifiability**: Repaired share verified against known public share
- **Privacy**: Individual contributions reveal nothing about helper shares
- **Coordination**: Commit-reveal prevents racing/selective disclosure
-/

import IceNine.Protocol.Repair
import IceNine.Protocol.Phase
import IceNine.Protocol.Lagrange
import Mathlib

namespace IceNine.Protocol.RepairCoord

open IceNine.Protocol

/-!
## Repair Coordination Phases

The repair protocol has distinct phases:
1. **Request**: Requester broadcasts repair request
2. **Commit**: Helpers commit to their contributions
3. **Reveal**: Helpers reveal contributions after all commits
4. **Verify**: Requester verifies reconstructed share
-/

/-- Repair protocol phases. -/
inductive RepairPhase
  | request  -- requester broadcasts request
  | commit   -- helpers commit to contributions
  | reveal   -- helpers reveal contributions
  | verify   -- requester verifies result
  | done     -- repair complete
deriving DecidableEq, Repr

/-!
## Message Types
-/

/-- Commitment to repair contribution. -/
structure ContribCommitMsg (S : Scheme) where
  sender : S.PartyId
  /-- Commitment to contribution value -/
  contribCommit : S.Commitment

/-- Reveal message for repair contribution. -/
structure ContribRevealMsg (S : Scheme) where
  sender : S.PartyId
  /-- The contribution (Lagrange-weighted share) -/
  contribution : S.Secret
  /-- Opening for commitment verification -/
  opening : S.Opening

/-- Verified contribution after commit-reveal. -/
structure VerifiedContrib (S : Scheme) where
  sender : S.PartyId
  contribution : S.Secret
  /-- The Lagrange coefficient used -/
  coefficient : S.Scalar

/-!
## Message Maps for Repair Coordination

Using MsgMap makes conflicting messages from the same helper **un-expressable**.
Each helper can submit at most one commit and one reveal per repair round.
-/

/-- Sender accessor for contribution commit messages. -/
def contribCommitSender {S : Scheme} (m : ContribCommitMsg S) : S.PartyId := m.sender

/-- Sender accessor for contribution reveal messages. -/
def contribRevealSender {S : Scheme} (m : ContribRevealMsg S) : S.PartyId := m.sender

/-- Map of contribution commit messages, keyed by sender. -/
abbrev ContribCommitMap (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] :=
  MsgMap S (ContribCommitMsg S)

/-- Map of contribution reveal messages, keyed by sender. -/
abbrev ContribRevealMap (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] :=
  MsgMap S (ContribRevealMsg S)

/-!
## Repair Coordination State

State uses MsgMap for commits and reveals to make conflicting messages un-expressable.
-/

/-- State for a repair coordination round.

    **CRDT Design**: Uses `MsgMap` for `commits` and `reveals` to ensure
    at most one message per helper. This makes conflicting messages un-expressable
    at the type level rather than requiring runtime checks. -/
structure RepairCoordState (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] where
  /-- Current phase -/
  phase : RepairPhase
  /-- The repair request -/
  request : RepairRequest S
  /-- Available helpers -/
  helpers : List S.PartyId
  /-- Threshold (minimum helpers needed) -/
  threshold : Nat
  /-- Commitments received from helpers (at most one per helper) -/
  commits : ContribCommitMap S
  /-- Reveals received from helpers (at most one per helper) -/
  reveals : ContribRevealMap S
  /-- Repaired share (after verification) -/
  repairedShare : Option S.Secret

/-- Create initial repair coordination state. -/
def initRepairCoord (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (request : RepairRequest S)
    (helpers : List S.PartyId)
    (threshold : Nat)
    : RepairCoordState S :=
  { phase := .request
    request := request
    helpers := helpers
    threshold := threshold
    commits := MsgMap.empty
    reveals := MsgMap.empty
    repairedShare := none }

/-!
## Protocol Functions
-/

/-- Check if enough helpers have committed. -/
def RepairCoordState.enoughCommits [BEq S.PartyId] [Hashable S.PartyId]
    (st : RepairCoordState S) : Bool :=
  st.commits.size ≥ st.threshold

/-- Check if all committed helpers have revealed. -/
def RepairCoordState.allRevealed [BEq S.PartyId] [Hashable S.PartyId]
    (st : RepairCoordState S) : Bool :=
  st.commits.senders.all (fun h => st.reveals.contains h)

/-!
## CRDT Merge Functions

These functions implement pure CRDT semantics: idempotent, commutative merge.
They always succeed and silently ignore duplicates (first-writer-wins).
Use these for replication/networking.
-/

/-- Process contribution commit (CRDT merge).
    Idempotent: duplicate messages from same sender are silently ignored.
    Non-helpers are silently ignored.
    Use `detectContribCommitConflict` separately if conflict detection is needed. -/
def processContribCommit (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    (st : RepairCoordState S) (msg : ContribCommitMsg S)
    : RepairCoordState S :=
  if st.phase = .commit then
    -- Only process if sender is a valid helper
    if st.helpers.contains msg.sender then
      let newSt := { st with commits := st.commits.insert contribCommitSender msg }
      -- Transition to reveal phase if enough commits
      if newSt.enoughCommits then { newSt with phase := .reveal }
      else newSt
    else st  -- Non-helper, no change
  else st

/-- Process contribution reveal (CRDT merge).
    Idempotent: duplicate messages from same sender are silently ignored.
    Invalid openings are silently rejected (no state change).
    Use `detectContribRevealConflict` and `validateContribReveal` separately if needed. -/
def processContribReveal (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.Commitment]
    (st : RepairCoordState S) (msg : ContribRevealMsg S)
    : RepairCoordState S :=
  if st.phase = .reveal then
    -- Verify commitment opens correctly
    match st.commits.get? msg.sender with
    | some c =>
        if S.commit (S.A msg.contribution) msg.opening = c.contribCommit then
          let newSt := { st with reveals := st.reveals.insert contribRevealSender msg }
          -- Transition to verify phase if all revealed
          if newSt.allRevealed then { newSt with phase := .verify }
          else newSt
        else st  -- Invalid opening, no change
    | none => st  -- No commit found, no change
  else st

/-!
## Conflict Detection (Validation Layer)

These functions detect anomalies without modifying state.
Use for auditing, logging, or when strict conflict handling is required.
Separate from CRDT merge to keep concerns clean.
-/

/-- Detect if a contribution commit conflicts with existing state.
    Returns the existing message if sender already committed. -/
def detectContribCommitConflict (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RepairCoordState S) (msg : ContribCommitMsg S)
    : Option (ContribCommitMsg S) :=
  st.commits.get? msg.sender

/-- Detect if a contribution reveal conflicts with existing state.
    Returns the existing message if sender already revealed. -/
def detectContribRevealConflict (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RepairCoordState S) (msg : ContribRevealMsg S)
    : Option (ContribRevealMsg S) :=
  st.reveals.get? msg.sender

/-- Validation errors for contribution commit processing. -/
inductive ContribCommitValidationError (S : Scheme)
  | wrongPhase (current : RepairPhase)
  | notHelper (sender : S.PartyId)
  | conflict (existing : ContribCommitMsg S)

/-- Validation errors for contribution reveal processing. -/
inductive ContribRevealValidationError (S : Scheme)
  | wrongPhase (current : RepairPhase)
  | noCommit (sender : S.PartyId)
  | invalidOpening (sender : S.PartyId)
  | conflict (existing : ContribRevealMsg S)

/-- Validate a contribution commit before processing.
    Returns error if validation fails, none if OK to process. -/
def validateContribCommit (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    (st : RepairCoordState S) (msg : ContribCommitMsg S)
    : Option (ContribCommitValidationError S) :=
  if st.phase ≠ .commit then
    some (.wrongPhase st.phase)
  else if !st.helpers.contains msg.sender then
    some (.notHelper msg.sender)
  else match detectContribCommitConflict S st msg with
    | some existing => some (.conflict existing)
    | none => none

/-- Validate a contribution reveal before processing.
    Returns error if validation fails, none if OK to process. -/
def validateContribReveal (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.Commitment]
    (st : RepairCoordState S) (msg : ContribRevealMsg S)
    : Option (ContribRevealValidationError S) :=
  if st.phase ≠ .reveal then
    some (.wrongPhase st.phase)
  else match st.commits.get? msg.sender with
    | none => some (.noCommit msg.sender)
    | some c =>
        if S.commit (S.A msg.contribution) msg.opening ≠ c.contribCommit then
          some (.invalidOpening msg.sender)
        else match detectContribRevealConflict S st msg with
          | some existing => some (.conflict existing)
          | none => none

/-- Process contribution commit with validation. Combines validation and CRDT merge.
    Use when you need both conflict detection and state update. -/
def processContribCommitValidated (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    (st : RepairCoordState S) (msg : ContribCommitMsg S)
    : RepairCoordState S × Option (ContribCommitValidationError S) :=
  let err := validateContribCommit S st msg
  (processContribCommit S st msg, err)

/-- Process contribution reveal with validation. Combines validation and CRDT merge.
    Use when you need both conflict detection and state update. -/
def processContribRevealValidated (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.Commitment]
    (st : RepairCoordState S) (msg : ContribRevealMsg S)
    : RepairCoordState S × Option (ContribRevealValidationError S) :=
  let err := validateContribReveal S st msg
  (processContribReveal S st msg, err)

/-- Aggregate revealed contributions to recover share. -/
def aggregateContributions (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (reveals : ContribRevealMap S) : S.Secret :=
  (reveals.toList.map (·.contribution)).sum

/-- Verify the repaired share against known public share.
    A(sk_i) must equal pk_i. -/
def verifyRepairedShareCoord (S : Scheme)
    (repairedSk : S.Secret) (expectedPk : S.Public) : Bool :=
  S.A repairedSk = expectedPk

/-- Complete repair: aggregate and verify. -/
def completeRepair (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.Public]
    (st : RepairCoordState S)
    : RepairCoordState S :=
  if st.phase = .verify then
    let repairedSk := aggregateContributions S st.reveals
    if S.A repairedSk = st.request.knownPk_i then
      { st with
        repairedShare := some repairedSk
        phase := .done }
    else st  -- Verification failed
  else st

/-!
## Helper's Local State

Each helper maintains state for participating in repair.
-/

/-- Helper's local state for repair participation. -/
structure HelperLocalState (S : Scheme) where
  /-- This helper's ID -/
  helperId : S.PartyId
  /-- This helper's key share -/
  keyShare : KeyShare S
  /-- Lagrange coefficient for this helper -/
  lagrangeCoeff : S.Scalar
  /-- Computed contribution (Lagrange-weighted share) -/
  contribution : S.Secret
  /-- Commitment to contribution -/
  commitment : S.Commitment
  /-- Opening for commitment -/
  opening : S.Opening

/-- Initialize helper state for repair participation. -/
def initHelper (S : Scheme)
    (keyShare : KeyShare S)
    (lagrangeCoeff : S.Scalar)
    (randomness : S.Opening)  -- for commitment
    : HelperLocalState S :=
  let contrib := lagrangeCoeff • keyShare.secret  -- use KeyShare.secret accessor
  let pubContrib := S.A contrib
  let commitment := S.commit pubContrib randomness
  { helperId := keyShare.pid
    keyShare := keyShare
    lagrangeCoeff := lagrangeCoeff
    contribution := contrib
    commitment := commitment
    opening := randomness }

/-- Generate commit message from helper state. -/
def helperCommitMsg (S : Scheme) (st : HelperLocalState S) : ContribCommitMsg S :=
  { sender := st.helperId
    contribCommit := st.commitment }

/-- Generate reveal message from helper state. -/
def helperRevealMsg (S : Scheme) (st : HelperLocalState S) : ContribRevealMsg S :=
  { sender := st.helperId
    contribution := st.contribution
    opening := st.opening }

/-!
## Full Repair Transcript

Transcripts extract List data from MsgMap state for archival and verification.
-/

/-- Complete repair coordination transcript. -/
structure RepairTranscript (S : Scheme) where
  /-- The repair request -/
  request : RepairRequest S
  /-- All commitment messages -/
  commits : List (ContribCommitMsg S)
  /-- All reveal messages -/
  reveals : List (ContribRevealMsg S)
  /-- Final repaired share (if successful) -/
  result : Option S.Secret
  /-- Verification status -/
  verified : Bool

/-- Create transcript from final state.
    Extracts lists from MsgMap for archival. -/
def createTranscript (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RepairCoordState S) : RepairTranscript S :=
  { request := st.request
    commits := st.commits.toList
    reveals := st.reveals.toList
    result := st.repairedShare
    verified := st.repairedShare.isSome }

/-!
## Lagrange Coefficient Computation

Helpers need to compute their Lagrange coefficients for the interpolation.
λ_j = Π_{m∈S, m≠j} (m / (m - j))

**Note**: Core Lagrange computation is in `Protocol/Lagrange.lean`.
These are convenience re-exports for repair-specific use.
-/

/-- Compute Lagrange coefficient for a party over a set of parties.
    Delegates to `Lagrange.coeffAtZero`. -/
def lagrangeCoefficient [Field F] [DecidableEq F]
    (partyScalar : F)
    (allScalars : List F)
    : F :=
  Lagrange.coeffAtZero partyScalar allScalars

/-- Compute all Lagrange coefficients for a set of parties.
    Delegates to `Lagrange.allCoeffsAtZero`. -/
def allLagrangeCoeffs [Field F] [DecidableEq F]
    (partyScalars : List F) : List (F × F) :=
  Lagrange.allCoeffsAtZero partyScalars

end IceNine.Protocol.RepairCoord
