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
## Dual Nonce Structure (FROST Pattern)

Following FROST, we use two nonces per signer instead of one:
- **Hiding nonce**: Protects against adaptive adversaries
- **Binding nonce**: Commits to the signing context (message + commitments)

This provides stronger security against adaptive chosen-message attacks,
which is particularly important for post-quantum settings where lattice-based
schemes may have different security margins.

**Security Rationale**:
- Single nonce: Adversary can adaptively choose message after seeing commitments
- Dual nonce: Binding nonce incorporates message, preventing adaptive attacks

Reference: FROST RFC (draft-irtf-cfrg-frost-15), Section 4.1
-/

/-- Secret nonces for a signing round.
    Both must be fresh random values from a CSPRNG.

    **CRITICAL**: Never reuse nonces across sessions. -/
structure SigningNonces (S : Scheme) where
  /-- Hiding nonce: protects signer from adaptive adversaries -/
  hiding  : S.Secret
  /-- Binding nonce: commits to signing context -/
  binding : S.Secret

/-- Public commitments derived from signing nonces.
    W_hiding = A(hiding), W_binding = A(binding) -/
structure SigningCommitments (S : Scheme) where
  /-- Public hiding commitment: A(hiding nonce) -/
  hiding  : S.Public
  /-- Public binding commitment: A(binding nonce) -/
  binding : S.Public

/-- Compute public commitments from secret nonces. -/
def SigningNonces.toCommitments (S : Scheme) (nonces : SigningNonces S) : SigningCommitments S :=
  { hiding := S.A nonces.hiding
    binding := S.A nonces.binding }

/-- Derive the effective nonce from dual nonces and binding factor.
    y = hiding + ρ·binding where ρ = H(msg, pk, commitments).

    This binding factor incorporates the signing context, preventing
    adaptive attacks where adversary chooses message after seeing commitments. -/
def SigningNonces.deriveEffective (S : Scheme)
    (nonces : SigningNonces S) (bindingFactor : S.Scalar) : S.Secret :=
  nonces.hiding + bindingFactor • nonces.binding

/-- Derive the effective public nonce.
    w = W_hiding + ρ·W_binding -/
def SigningCommitments.deriveEffective (S : Scheme)
    (commits : SigningCommitments S) (bindingFactor : S.Scalar) : S.Public :=
  commits.hiding + bindingFactor • commits.binding

/-!
## Binding Factor Computation

The binding factor ρ_i binds each signer's nonce to the full signing context:
- Message being signed
- Public key
- All signers' commitments
- This signer's identifier

This prevents an adversary from adaptively choosing the message after
seeing nonce commitments, and ensures each signer's contribution is
bound to the specific signing session.

Reference: FROST RFC Section 4.4
-/

/-- Binding factor for a specific signer.
    Computed as H("binding", msg, pk, all_commitments, signer_id).

    **NOTE**: The actual hash computation depends on the Scheme's hash function.
    This structure carries the computed binding factor for use in signing. -/
structure BindingFactor (S : Scheme) where
  pid    : S.PartyId
  factor : S.Scalar

/-- Collection of binding factors for all signers in a session. -/
structure BindingFactors (S : Scheme) where
  factors : List (BindingFactor S)

/-- Look up binding factor for a specific party. -/
def BindingFactors.get [DecidableEq S.PartyId]
    (bf : BindingFactors S) (pid : S.PartyId) : Option S.Scalar :=
  (bf.factors.find? (·.pid = pid)).map (·.factor)

/-!
## State and Message Types
-/

/-- Party's local state during signing (dual nonce). -/
structure SignLocalState (S : Scheme) where
  share   : KeyShare S           -- party's long-term credential from DKG
  msg     : S.Message            -- message being signed
  session : Nat                  -- unique session identifier
  nonces  : SigningNonces S      -- dual ephemeral nonces (NEVER reuse!)
  commits : SigningCommitments S -- public nonce commitments
  openW   : S.Opening            -- commitment randomness for hiding commitment

/-- Round 1 message: commitment to ephemeral nonces.
    Contains both hiding and binding public commitments. -/
structure SignCommitMsg (S : Scheme) where
  sender   : S.PartyId
  session  : Nat
  /-- Commitment to hiding public nonce (hash-based commitment) -/
  commitW  : S.Commitment
  /-- Public hiding commitment W_hiding = A(hiding nonce) -/
  hiding   : S.Public
  /-- Public binding commitment W_binding = A(binding nonce) -/
  binding  : S.Public

/-- Reveal message: party discloses opening for verification.
    With dual nonces, the public commitments are sent in Round 1,
    so only the opening is needed for verification. -/
structure SignRevealWMsg (S : Scheme) where
  sender  : S.PartyId
  session : Nat
  /-- Opening for the hiding commitment verification -/
  opening : S.Opening

/-- Lagrange coefficient for party i over signer set S. -/
structure LagrangeCoeff (S : Scheme) where
  pid    : S.PartyId
  lambda : S.Scalar

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

/-- Abort state for distributed coordination. -/
structure SignAbortState (S : Scheme) where
  abortedSession : Option Nat
  abortVotes : Finset S.PartyId
  reasons : List (S.PartyId × AbortReason S.PartyId)

/-- CRDT merge for abort state. -/
instance (S : Scheme) [DecidableEq S.PartyId] : Join (SignAbortState S) :=
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
## SigningPackage (FROST Pattern)

The SigningPackage bundles all context needed for signing into a single
structure. This provides a cleaner API and makes it harder to misuse
the protocol by passing inconsistent arguments.

Reference: FROST RFC Section 5.2
-/

/-- Signing package bundling all context for a signing session.
    This aggregates the data that would otherwise be passed as separate arguments. -/
structure SigningPackage (S : Scheme) where
  /-- Unique session identifier -/
  session : Nat
  /-- Message being signed -/
  message : S.Message
  /-- Global public key -/
  publicKey : S.Public
  /-- All signers' commitments (collected from Round 1) -/
  commitments : List (SignCommitMsg S)
  /-- Computed binding factors for all signers -/
  bindingFactors : BindingFactors S
  /-- Signer set (party IDs participating) -/
  signerSet : List S.PartyId

/-- Create a signing package with validation.
    Returns none if commitments don't match signer set. -/
def SigningPackage.create [DecidableEq S.PartyId]
    (session : Nat)
    (message : S.Message)
    (publicKey : S.Public)
    (commitments : List (SignCommitMsg S))
    (bindingFactors : BindingFactors S)
    : Option (SigningPackage S) :=
  let signerSet := commitments.map (·.sender)
  if signerSet.Nodup then
    some {
      session := session
      message := message
      publicKey := publicKey
      commitments := commitments
      bindingFactors := bindingFactors
      signerSet := signerSet
    }
  else none

/-- Get a specific signer's commitments from the package. -/
def SigningPackage.getCommitment [DecidableEq S.PartyId]
    (pkg : SigningPackage S) (pid : S.PartyId) : Option (SignCommitMsg S) :=
  pkg.commitments.find? (·.sender = pid)

/-- Get binding factor for a specific signer. -/
def SigningPackage.getBindingFactor [DecidableEq S.PartyId]
    (pkg : SigningPackage S) (pid : S.PartyId) : Option S.Scalar :=
  pkg.bindingFactors.get pid

/-- Validate that all expected signers have commitments. -/
def SigningPackage.isComplete [DecidableEq S.PartyId]
    (pkg : SigningPackage S) : Bool :=
  pkg.signerSet.all fun pid =>
    pkg.commitments.any (·.sender = pid)

/-- Number of signers in this package. -/
def SigningPackage.signerCount (pkg : SigningPackage S) : Nat :=
  pkg.signerSet.length

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

/-!
## Batch Verification

Infrastructure for verifying multiple signatures efficiently using
a single aggregated equation check with random weights.

**Mathematical Basis**:
For k signatures with random weights α₁, ..., αₖ, verify:
  Σⱼ αⱼ·(A(zⱼ) - cⱼ·pk) = Σⱼ αⱼ·wⱼ

This is faster than k individual verifications when implemented
with a single multiscalar multiplication.

Reference: Bellare et al. "Batch Verification with Applications to
Cryptography and Checking" (LATIN 1998)
-/

/-- Entry in a batch verification context. -/
structure BatchEntry (S : Scheme) where
  /-- Message that was signed -/
  message : S.Message
  /-- Signature to verify -/
  signature : Signature S
  /-- Public key (may differ per entry for multi-key batches) -/
  publicKey : S.Public

/-- Batch verification context accumulating entries for batch check. -/
structure BatchVerificationContext (S : Scheme) where
  /-- Entries to verify -/
  entries : List (BatchEntry S)
  /-- Random weights (generated during verification) -/
  weights : List S.Scalar

/-- Empty batch context. -/
def BatchVerificationContext.empty (S : Scheme) : BatchVerificationContext S :=
  { entries := [], weights := [] }

/-- Add an entry to the batch. -/
def BatchVerificationContext.add
    (ctx : BatchVerificationContext S)
    (entry : BatchEntry S)
    (weight : S.Scalar)
    : BatchVerificationContext S :=
  { entries := entry :: ctx.entries
    weights := weight :: ctx.weights }

/-- Number of entries in the batch. -/
def BatchVerificationContext.size (ctx : BatchVerificationContext S) : Nat :=
  ctx.entries.length

/-- Result of batch verification. -/
inductive BatchVerificationResult (S : Scheme)
  | allValid
      -- All signatures verified successfully
  | batchFailed (entries : List (BatchEntry S))
      -- Batch check failed, entries need individual verification
  | individualFailures (failed : List (BatchEntry S × Nat))
      -- Individual verification identified specific failures (entry, index)
  deriving Repr

/-- Configuration for batch verification. -/
structure BatchVerifyConfig where
  /-- Minimum entries to use batch verification (below this, verify individually) -/
  minBatchSize : Nat := 2
  /-- Bit length for random weights (higher = more security, slower) -/
  weightBits : Nat := 128
  deriving Repr

/-- Default batch verification configuration. -/
def BatchVerifyConfig.default : BatchVerifyConfig :=
  { minBatchSize := 2, weightBits := 128 }

end IceNine.Protocol
