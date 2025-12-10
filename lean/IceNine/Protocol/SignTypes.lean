/-
# Signing Types

Core type definitions for the threshold signing protocol.
Split from Sign.lean for modularity.

See Sign.lean for the full protocol documentation and API guidance.
-/

import IceNine.Protocol.Core
import IceNine.Protocol.Phase
import Mathlib

namespace IceNine.Protocol

open List

/-!
## Session Tracking

Session IDs must be unique to prevent nonce reuse attacks.
-/

/-- Tracks used session IDs to prevent nonce reuse.
    Each party maintains this state across signing sessions. -/
structure SessionTracker (S : Scheme) where
  /-- Set of session IDs that have been used -/
  usedSessions : Finset Nat
  /-- Party ID this tracker belongs to -/
  partyId : S.PartyId
deriving Repr

/-- Check if a session ID is fresh (not previously used) -/
def SessionTracker.isFresh (tracker : SessionTracker S) (session : Nat) : Bool :=
  session ∉ tracker.usedSessions

/-- Mark a session as used (call after committing to nonce) -/
def SessionTracker.markUsed (tracker : SessionTracker S) (session : Nat)
    : SessionTracker S :=
  { tracker with usedSessions := tracker.usedSessions.insert session }

/-- Create empty tracker for a party -/
def SessionTracker.empty (S : Scheme) (pid : S.PartyId) : SessionTracker S :=
  { usedSessions := ∅, partyId := pid }

/-- Session validation result -/
inductive SessionCheckResult
  | ok                           -- session is fresh, safe to proceed
  | alreadyUsed (session : Nat)  -- DANGER: session was used before
  | invalidId                    -- session ID is malformed
deriving DecidableEq, Repr

/-- Validate session before starting signing -/
def checkSession (tracker : SessionTracker S) (session : Nat)
    : SessionCheckResult :=
  if tracker.isFresh session then .ok
  else .alreadyUsed session

/-!
## Nonce Registry

Global view of nonce commitments for reuse detection.
-/

/-- Nonce registry for detecting reuse across the network. -/
structure NonceRegistry (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment] where
  /-- Primary index: (partyId, session) → commitment -/
  bySession : Std.HashMap (S.PartyId × Nat) S.Commitment
  /-- Reverse index: (partyId, commitment) → list of sessions -/
  byCommitment : Std.HashMap (S.PartyId × S.Commitment) (List Nat)
deriving Repr

/-- Empty nonce registry. -/
def NonceRegistry.empty (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    : NonceRegistry S :=
  { bySession := Std.HashMap.empty
    byCommitment := Std.HashMap.empty }

/-- Check if a nonce commitment was seen before. -/
def NonceRegistry.hasCommitment
    (reg : NonceRegistry S)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (pid : S.PartyId) (session : Nat) (commit : S.Commitment) : Bool :=
  match reg.bySession.get? (pid, session) with
  | some c => c == commit
  | none => false

/-- Check if a (party, session) pair exists. -/
def NonceRegistry.hasSession
    (reg : NonceRegistry S)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (pid : S.PartyId) (session : Nat) : Bool :=
  reg.bySession.contains (pid, session)

/-- Record a nonce commitment. -/
def NonceRegistry.record
    (reg : NonceRegistry S)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (pid : S.PartyId) (session : Nat) (commit : S.Commitment) : NonceRegistry S :=
  let newBySession := reg.bySession.insert (pid, session) commit
  let key := (pid, commit)
  let sessions := reg.byCommitment.get? key |>.getD []
  let newByCommitment := reg.byCommitment.insert key (session :: sessions)
  { bySession := newBySession
    byCommitment := newByCommitment }

/-- Detect if same nonce was used in different sessions. -/
def NonceRegistry.detectReuse
    (reg : NonceRegistry S)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (pid : S.PartyId) (commit : S.Commitment) : Option (Nat × Nat) :=
  match reg.byCommitment.get? (pid, commit) with
  | some (s1 :: s2 :: _) => if s1 ≠ s2 then some (s1, s2) else none
  | _ => none

/-- Get all commitments as a list. -/
def NonceRegistry.toList
    (reg : NonceRegistry S)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    : List (S.PartyId × Nat × S.Commitment) :=
  reg.bySession.toList.map fun ((pid, session), commit) => (pid, session, commit)

/-!
## State and Message Types
-/

/-- Party's local state during signing. -/
structure SignLocalState (S : Scheme) where
  share   : KeyShare S   -- party's long-term credential from DKG
  msg     : S.Message    -- message being signed
  session : Nat          -- unique session identifier
  y_i     : S.Secret     -- ephemeral nonce (NEVER reuse!)
  w_i     : S.Public     -- public nonce = A(y_i)
  openW   : S.Opening    -- commitment randomness
deriving Repr

/-- Round 1 message: commitment to ephemeral nonce. -/
structure SignCommitMsg (S : Scheme) where
  sender  : S.PartyId
  session : Nat
  commitW : S.Commitment
deriving Repr

/-- Reveal message: party discloses w_i and opening. -/
structure SignRevealWMsg (S : Scheme) where
  sender  : S.PartyId
  session : Nat
  w_i     : S.Public
  opening : S.Opening
deriving Repr

/-- Lagrange coefficient for party i over signer set S. -/
structure LagrangeCoeff (S : Scheme) where
  pid    : S.PartyId
  lambda : S.Scalar
deriving Repr

/-!
## Error Types
-/

/-- Signing failure modes. -/
inductive SignError (PartyId : Type u) where
  | lengthMismatch : SignError PartyId
  | participantMismatch : PartyId → SignError PartyId
  | duplicateParticipants : SignError PartyId
  | commitMismatch : PartyId → SignError PartyId
  | sessionMismatch : Nat → Nat → SignError PartyId
  | normCheckFailed : PartyId → SignError PartyId
  | maxRetriesExceeded : PartyId → SignError PartyId
  | sessionAborted : Nat → SignError PartyId
deriving DecidableEq

/-- Abort reason for detailed error reporting -/
inductive AbortReason (PartyId : Type u) where
  | normBoundExceeded : PartyId → Nat → AbortReason PartyId
  | maxRetriesReached : PartyId → AbortReason PartyId
  | coordinationFailure : AbortReason PartyId
  | timeout : AbortReason PartyId
deriving DecidableEq, Repr

/-- Session abort notification. -/
structure SignAbortMsg (S : Scheme) where
  sender  : S.PartyId
  session : Nat
  reason  : AbortReason S.PartyId
deriving Repr

/-- Abort state for distributed coordination. -/
structure SignAbortState (S : Scheme) where
  abortedSession : Option Nat
  abortVotes : Finset S.PartyId
  reasons : List (S.PartyId × AbortReason S.PartyId)
deriving Repr

/-- CRDT merge for abort state. -/
instance (S : Scheme) : Join (SignAbortState S) :=
  ⟨fun a b => {
    abortedSession := a.abortedSession <|> b.abortedSession
    abortVotes := a.abortVotes ∪ b.abortVotes
    reasons := a.reasons ++ b.reasons
  }⟩

/-- Empty abort state. -/
def SignAbortState.empty (S : Scheme) : SignAbortState S :=
  { abortedSession := none, abortVotes := ∅, reasons := [] }

/-- Create abort state from a single message. -/
def SignAbortState.fromMsg (S : Scheme) (msg : SignAbortMsg S) : SignAbortState S :=
  { abortedSession := some msg.session
    abortVotes := {msg.sender}
    reasons := [(msg.sender, msg.reason)] }

/-- Minimum abort threshold to prevent griefing. -/
def minAbortThreshold (totalParties : Nat) : Nat :=
  (totalParties + 1) / 2 + 1

/-- Check if session should be considered aborted. -/
def SignAbortState.isAborted (state : SignAbortState S) (threshold : Nat) (totalParties : Nat) : Bool :=
  let effectiveThreshold := max threshold (minAbortThreshold totalParties)
  state.abortVotes.card ≥ effectiveThreshold

/-- Safe abort check using minimum threshold. -/
def SignAbortState.isSafelyAborted (state : SignAbortState S) (totalParties : Nat) : Bool :=
  state.abortVotes.card ≥ minAbortThreshold totalParties

/-- Create abort message when norm check fails. -/
def mkNormAbortMsg (S : Scheme) (pid : S.PartyId) (session : Nat) (attempt : Nat)
    : SignAbortMsg S :=
  { sender := pid, session := session, reason := .normBoundExceeded pid attempt }

/-- Create abort message when max retries exceeded. -/
def mkMaxRetryAbortMsg (S : Scheme) (pid : S.PartyId) (session : Nat)
    : SignAbortMsg S :=
  { sender := pid, session := session, reason := .maxRetriesReached pid }

/-!
## Signature Types
-/

/-- Final signature. -/
structure Signature (S : Scheme) where
  z       : S.Secret
  c       : S.Challenge
  Sset    : List S.PartyId
  commits : List S.Commitment

/-- Signing attempt outcome -/
inductive SignAttemptResult (S : Scheme)
  | success (msg : SignShareMsg S)
  | retry
  | abort
deriving Repr

/-- Maximum retry attempts before abort. -/
def maxSigningAttempts : Nat := 16

/-- Final signature wrapper for CRDT done state. -/
structure SignatureDone (S : Scheme) where
  sig : Signature S

/-- DoneState alias for CRDT phase state. -/
abbrev DoneState := SignatureDone

/-- DoneState merge: idempotent. -/
instance (S : Scheme) : Join (DoneState S) :=
  ⟨fun a _ => a⟩

instance (S : Scheme) : LE (DoneState S) := ⟨fun _ _ => True⟩

end IceNine.Protocol
