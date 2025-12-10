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
deriving Repr

/-- Reveal message for repair contribution. -/
structure ContribRevealMsg (S : Scheme) where
  sender : S.PartyId
  /-- The contribution (Lagrange-weighted share) -/
  contribution : S.Secret
  /-- Opening for commitment verification -/
  opening : S.Opening
deriving Repr

/-- Verified contribution after commit-reveal. -/
structure VerifiedContrib (S : Scheme) where
  sender : S.PartyId
  contribution : S.Secret
  /-- The Lagrange coefficient used -/
  coefficient : S.Scalar
deriving Repr

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
deriving Repr

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

/-- Result of processing a contribution commit. -/
inductive ContribCommitResult (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
  | success (newSt : RepairCoordState S)
  | conflict (existing : ContribCommitMsg S)
  | notHelper
  | wrongPhase
deriving Repr

/-- Process a commit from a helper with conflict detection. -/
def processContribCommitStrict (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    (st : RepairCoordState S) (msg : ContribCommitMsg S)
    : ContribCommitResult S :=
  if st.phase = .commit then
    -- Verify sender is a valid helper
    if st.helpers.contains msg.sender then
      match st.commits.tryInsert contribCommitSender msg with
      | .success newCommits =>
          let newSt := { st with commits := newCommits }
          -- Transition to reveal phase if enough commits
          if newSt.enoughCommits then
            .success { newSt with phase := .reveal }
          else .success newSt
      | .conflict existing => .conflict existing
    else .notHelper
  else .wrongPhase

/-- Process a commit from a helper (CRDT mode: ignores duplicates). -/
def processContribCommit (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    (st : RepairCoordState S) (msg : ContribCommitMsg S)
    : RepairCoordState S :=
  if st.phase = .commit then
    -- Verify sender is a valid helper
    if st.helpers.contains msg.sender then
      let newSt := { st with commits := st.commits.insert contribCommitSender msg }
      -- Transition to reveal phase if enough commits
      if newSt.enoughCommits then
        { newSt with phase := .reveal }
      else newSt
    else st  -- Ignore non-helper
  else st

/-- Result of processing a contribution reveal. -/
inductive ContribRevealResult (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
  | success (newSt : RepairCoordState S)
  | conflict (existing : ContribRevealMsg S)
  | invalidOpening
  | noCommit
  | wrongPhase
deriving Repr

/-- Process a reveal from a helper with conflict detection. -/
def processContribRevealStrict (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.Commitment]
    (st : RepairCoordState S) (msg : ContribRevealMsg S)
    : ContribRevealResult S :=
  if st.phase = .reveal then
    -- Verify commitment opens correctly
    match st.commits.get? msg.sender with
    | some c =>
        if S.commit (S.A msg.contribution) msg.opening = c.contribCommit then
          match st.reveals.tryInsert contribRevealSender msg with
          | .success newReveals =>
              let newSt := { st with reveals := newReveals }
              -- Transition to verify phase if all revealed
              if newSt.allRevealed then
                .success { newSt with phase := .verify }
              else .success newSt
          | .conflict existing => .conflict existing
        else .invalidOpening
    | none => .noCommit
  else .wrongPhase

/-- Process a reveal from a helper (CRDT mode). -/
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
          if newSt.allRevealed then
            { newSt with phase := .verify }
          else newSt
        else st  -- Invalid opening
    | none => st  -- No commit found
  else st

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
deriving Repr

/-- Initialize helper state for repair participation. -/
def initHelper (S : Scheme)
    (keyShare : KeyShare S)
    (lagrangeCoeff : S.Scalar)
    (randomness : S.Opening)  -- for commitment
    : HelperLocalState S :=
  let contrib := lagrangeCoeff • keyShare.sk_i
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
deriving Repr

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
-/

/-- Compute Lagrange coefficient for a party over a set of parties.
    Assumes party IDs can be converted to scalars. -/
def lagrangeCoefficient [Field F] [DecidableEq F]
    (partyScalar : F)           -- this party's scalar representation
    (otherScalars : List F)     -- other parties' scalars
    : F :=
  otherScalars.foldl (fun acc m =>
    if m = partyScalar then acc
    else acc * (m / (m - partyScalar))) 1

/-- Compute all Lagrange coefficients for a set of parties. -/
def allLagrangeCoeffs [Field F] [DecidableEq F]
    (partyScalars : List F) : List (F × F) :=  -- (party, coefficient) pairs
  partyScalars.map fun p =>
    let others := partyScalars
    (p, lagrangeCoefficient p others)

end IceNine.Protocol.RepairCoord
