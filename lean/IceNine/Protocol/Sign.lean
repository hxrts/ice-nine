/-
# Threshold Signing Protocol

Two-round threshold signing following the Schnorr pattern:
  Round 1: Parties commit to ephemeral nonces
  Round 2: Parties reveal nonces, compute challenge, produce partial signatures
  Aggregation: Combine partials into final signature

Supports both n-of-n (all parties) and t-of-n (threshold) signing.
Security proofs in `Security/Sign`.
-/

import IceNine.Protocol.Core
import Mathlib

namespace IceNine.Protocol

open List

/-!
## State and Message Types

Each signing session has a unique session ID. Parties maintain local state
with their ephemeral nonce and exchange commit/reveal/share messages.
-/

/-!
## Session and Nonce Safety

**CRITICAL**: Nonce reuse is catastrophic for Schnorr-style signatures.
If the same nonce y is used with two different challenges c₁, c₂:
  z₁ = y + c₁·sk
  z₂ = y + c₂·sk
Then: sk = (z₁ - z₂) / (c₁ - c₂)  -- secret key recovered!

We track used sessions to prevent this attack vector.
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

/-- Nonce registry for detecting reuse across the network.
    This is a global view; in practice, parties only see their own history. -/
structure NonceRegistry (S : Scheme) where
  /-- Map from (partyId, session) to nonce commitment -/
  commitments : List (S.PartyId × Nat × S.Commitment)
deriving Repr

/-- Check if a nonce commitment was seen before -/
def NonceRegistry.hasCommitment (reg : NonceRegistry S) [DecidableEq S.PartyId]
    [DecidableEq S.Commitment]
    (pid : S.PartyId) (session : Nat) (commit : S.Commitment) : Bool :=
  reg.commitments.any (fun (p, s, c) => p = pid ∧ s = session ∧ c = commit)

/-- Record a nonce commitment -/
def NonceRegistry.record (reg : NonceRegistry S)
    (pid : S.PartyId) (session : Nat) (commit : S.Commitment) : NonceRegistry S :=
  { reg with commitments := (pid, session, commit) :: reg.commitments }

/-- Detect if same nonce was used in different sessions (attack detection) -/
def NonceRegistry.detectReuse (reg : NonceRegistry S) [DecidableEq S.PartyId]
    [DecidableEq S.Commitment]
    (pid : S.PartyId) (commit : S.Commitment) : Option (Nat × Nat) :=
  -- Find two different sessions with same commitment from same party
  let matching := reg.commitments.filter (fun (p, _, c) => p = pid ∧ c = commit)
  match matching with
  | (_, s1, _) :: (_, s2, _) :: _ => if s1 ≠ s2 then some (s1, s2) else none
  | _ => none

/-!
## State and Message Types

Each signing session has a unique session ID. Parties maintain local state
with their ephemeral nonce and exchange commit/reveal/share messages.
-/

/-- Party's local state during signing. Contains ephemeral nonce y_i
    (sampled fresh each session) and commitment data. -/
structure SignLocalState (S : Scheme) :=
  (share   : KeyShare S)   -- party's long-term credential from DKG
  (msg     : S.Message)    -- message being signed
  (session : Nat)          -- unique session identifier
  (y_i     : S.Secret)     -- ephemeral nonce (NEVER reuse across sessions!)
  (w_i     : S.Public)     -- public nonce = A(y_i)
  (openW   : S.Opening)    -- commitment randomness
deriving Repr

/-- Round 1 message: commitment to ephemeral nonce w_i.
    Hiding w_i until all commit prevents adaptive attacks. -/
structure SignCommitMsg (S : Scheme) :=
  (sender  : S.PartyId)
  (session : Nat)
  (commitW : S.Commitment)
deriving Repr

/-- Reveal message: party discloses w_i and opening after all commits received.
    Others verify: commit(w_i, opening) = commitW from round 1. -/
structure SignRevealWMsg (S : Scheme) :=
  (sender  : S.PartyId)
  (session : Nat)
  (w_i     : S.Public)
  (opening : S.Opening)
deriving Repr

/-- Round 2 message: partial signature z_i = y_i + c·sk_i.
    Ephemeral nonce y_i masks the secret share contribution. -/
structure SignShareMsg (S : Scheme) :=
  (sender  : S.PartyId)
  (session : Nat)
  (z_i     : S.Secret)
deriving Repr

/-- Lagrange coefficient for party i over signer set S.
    In t-of-n signing, partials are weighted: z = Σ λ_i·z_i. -/
structure LagrangeCoeff (S : Scheme) :=
  (pid    : S.PartyId)
  (lambda : S.Scalar)     -- λ_i = Π_{j≠i} j/(j-i)
deriving Repr

/-!
## Error Handling

Structured errors identify exactly what went wrong during signing.
Includes abort conditions from rejection sampling failures.
-/

/-- Signing failure modes with identifying information. -/
inductive SignError (PartyId : Type u) where
  | lengthMismatch : SignError PartyId                 -- message count mismatch
  | participantMismatch : PartyId → SignError PartyId  -- unexpected party
  | duplicateParticipants : SignError PartyId          -- same party twice
  | commitMismatch : PartyId → SignError PartyId       -- reveal doesn't match commit
  | sessionMismatch : Nat → Nat → SignError PartyId    -- wrong session ID
  | normCheckFailed : PartyId → SignError PartyId      -- party's z_i failed norm bound
  | maxRetriesExceeded : PartyId → SignError PartyId   -- party exceeded retry limit
  | sessionAborted : Nat → SignError PartyId           -- session was aborted
  deriving DecidableEq

/-- Abort reason for detailed error reporting -/
inductive AbortReason (PartyId : Type u) where
  | normBoundExceeded : PartyId → Nat → AbortReason PartyId  -- party, attempt count
  | maxRetriesReached : PartyId → AbortReason PartyId
  | coordinationFailure : AbortReason PartyId                -- parties disagreed on retry
  | timeout : AbortReason PartyId
  deriving DecidableEq, Repr

/-- Session abort notification broadcast to all parties -/
structure SignAbortMsg (S : Scheme) where
  sender  : S.PartyId
  session : Nat
  reason  : AbortReason S.PartyId
deriving Repr

/-- Abort state tracked in CRDT for distributed coordination -/
structure SignAbortState (S : Scheme) where
  /-- Session that was aborted (if any) -/
  abortedSession : Option Nat
  /-- Parties that requested abort -/
  abortVotes : List S.PartyId
  /-- Abort reasons from each party -/
  reasons : List (AbortReason S.PartyId)
deriving Repr

/-- CRDT merge for abort state: union votes and reasons -/
instance (S : Scheme) : Join (SignAbortState S) :=
  ⟨fun a b => {
    abortedSession := a.abortedSession <|> b.abortedSession
    abortVotes := a.abortVotes ++ b.abortVotes
    reasons := a.reasons ++ b.reasons
  }⟩

/-- Empty abort state (no abort in progress) -/
def SignAbortState.empty (S : Scheme) : SignAbortState S :=
  { abortedSession := none, abortVotes := [], reasons := [] }

/-- Create abort state from a single abort message -/
def SignAbortState.fromMsg (S : Scheme) (msg : SignAbortMsg S) : SignAbortState S :=
  { abortedSession := some msg.session
    abortVotes := [msg.sender]
    reasons := [msg.reason] }

/-- Check if session should be considered aborted.
    Requires threshold of parties to agree (prevents single-party griefing). -/
def SignAbortState.isAborted (state : SignAbortState S) (threshold : Nat) : Bool :=
  state.abortVotes.length ≥ threshold

/-- Create abort message when norm check fails -/
def mkNormAbortMsg (S : Scheme) (pid : S.PartyId) (session : Nat) (attempt : Nat)
    : SignAbortMsg S :=
  { sender := pid
    session := session
    reason := .normBoundExceeded pid attempt }

/-- Create abort message when max retries exceeded -/
def mkMaxRetryAbortMsg (S : Scheme) (pid : S.PartyId) (session : Nat)
    : SignAbortMsg S :=
  { sender := pid
    session := session
    reason := .maxRetriesReached pid }

/-- Predicate capturing a valid signing transcript.
    All messages consistent, commitments verified, sessions match. -/
structure ValidSignTranscript (S : Scheme)
  (Sset : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S)) : Prop :=
  (len_comm_reveal : commits.length = reveals.length)
  (len_reveal_share : reveals.length = shares.length)
  (pids_nodup : (commits.map (·.sender)).Nodup)
  (pids_eq : commits.map (·.sender) = Sset)
  (commit_open_ok :
    List.Forall2 (fun c r => c.sender = r.sender ∧ S.commit r.w_i r.opening = c.commitW) commits reveals)
  (sessions_ok :
    let sess := (commits.head?.map (·.session)).getD 0;
    ∀ sh ∈ shares, sh.session = sess)

/-!
## Lagrange Interpolation

For t-of-n threshold signing, partial signatures are weighted by
Lagrange coefficients to reconstruct the full signature.
-/

/-- Compute Lagrange coefficient λ_i for party i evaluating at 0.
    λ_i = Π_{j∈S, j≠i} x_j / (x_j - x_i) where x_k = pidToScalar(k). -/
def lagrangeCoeffAtZero
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (pidToScalar : S.PartyId → S.Scalar)
  (Sset : List S.PartyId) (i : S.PartyId) : S.Scalar :=
  let xi := pidToScalar i
  let others := Sset.erase i
  -- Return 0 if duplicate scalar values (would cause division by zero)
  if hdup : (others.any (fun j => pidToScalar j = xi)) then 0 else
    (others.map (fun j => let xj := pidToScalar j; xj / (xj - xi))).prod

/-- Compute all Lagrange coefficients for a signer set. -/
def lagrangeCoeffs
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (pidToScalar : S.PartyId → S.Scalar)
  (Sset : List S.PartyId) : List (LagrangeCoeff S) :=
  Sset.map (fun pid => { pid := pid, lambda := lagrangeCoeffAtZero S pidToScalar Sset pid })

/-!
## Round 1: Nonce Commitment

Party samples ephemeral nonce y_i, computes w_i = A(y_i), commits to w_i.
The commitment hides w_i until all parties have committed.
-/

/-- Round 1: sample nonce, commit to public nonce.
    Returns local state and commit message for broadcast. -/
def signRound1
  (S : Scheme)
  (ks      : KeyShare S)  -- party's DKG credential
  (m       : S.Message)   -- message to sign
  (session : Nat)         -- unique session ID
  (y_i     : S.Secret)    -- pre-sampled ephemeral nonce
  (openW   : S.Opening)   -- commitment randomness
  : SignLocalState S × SignCommitMsg S :=
-- Derive public nonce from secret nonce
let w_i : S.Public := S.A y_i
-- Commit to hide w_i until reveal phase
let com : S.Commitment := S.commit w_i openW
-- Bundle local state (includes secret nonce)
let st  : SignLocalState S :=
  { share   := ks,
    msg     := m,
    session := session,
    y_i     := y_i,
    w_i     := w_i,
    openW   := openW }
-- Bundle broadcast message
let msg1 : SignCommitMsg S :=
  { from    := ks.pid,
    session := session,
    commitW := com }
(st, msg1)

/-!
## Challenge Derivation

After all reveals, compute aggregate nonce w = Σ w_i and derive
challenge c = H(m, pk, S, commits, w) via Fiat-Shamir.
-/

/-- Compute Fiat-Shamir challenge from transcript.
    Returns (challenge, aggregate_nonce). -/
def computeChallenge
  (S     : Scheme)
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  : Option (S.Challenge × S.Public) :=
  -- Aggregate nonces: w = Σ w_i
  let w : S.Public := (reveals.map (·.w_i)).sum
  -- Hash full transcript to derive challenge
  let c : S.Challenge := S.hash m pk Sset (commits.map (fun cmsg => cmsg.commitW)) w
  some (c, w)

/-!
## Round 2: Partial Signature

Party computes z_i = y_i + c·sk_i. The ephemeral nonce y_i masks the
secret share so z_i reveals nothing about sk_i alone.

### Rejection Sampling

In lattice signatures, the response z must have bounded norm to prevent
leakage. If ||z|| is too large, the party must:
1. Sample a fresh nonce y'
2. Recompute w' = A(y') and get new challenge c' = H(m, pk, w')
3. Try again with z' = y' + c'·s

This requires coordination - all parties must restart together.
Expected attempts: ~4 for Dilithium parameters.

**Reference**: Lyubashevsky, "Fiat-Shamir with Aborts", ASIACRYPT 2009.
-/

/-- Maximum retry attempts before declaring abort.
    Dilithium expects ~4 attempts; we allow more for safety margin. -/
def maxSigningAttempts : Nat := 16

/-- Signing attempt outcome -/
inductive SignAttemptResult (S : Scheme)
  | success (msg : SignShareMsg S)  -- z_i passed norm check
  | retry                           -- need fresh nonce, try again
  | abort                           -- max attempts exceeded
deriving Repr

/-- State for rejection sampling loop -/
structure SignRetryState (S : Scheme) where
  /-- Base state (share, message, session) -/
  base      : SignLocalState S
  /-- Current attempt number (1-indexed) -/
  attempt   : Nat
  /-- Challenge (fixed across retries in single-signer, varies in threshold) -/
  challenge : S.Challenge
deriving Repr

/-- Round 2: compute partial signature z_i = y_i + c·sk_i.
    Returns None if z_i fails norm check (lattice security). -/
def signRound2
  (S : Scheme)
  (st : SignLocalState S)  -- local state from round 1
  (c  : S.Challenge)       -- challenge from computeChallenge
  : Option (SignShareMsg S) :=
  -- z_i = y_i + c·sk_i (nonce masks secret contribution)
  let z_i : S.Secret := st.y_i + c • st.share.sk_i
  -- Reject if norm too large (prevents leakage in lattice setting)
  if h : S.normOK z_i then
    some { from    := st.share.pid,
           session := st.session,
           z_i     := z_i }
  else
    none

/-- Single attempt at signing with norm check.
    Returns result indicating success, need for retry, or abort. -/
def signAttempt
  (S : Scheme)
  (retryState : SignRetryState S)
  : SignAttemptResult S :=
  if retryState.attempt > maxSigningAttempts then
    .abort
  else
    let z_i := retryState.base.y_i + retryState.challenge • retryState.base.share.sk_i
    if h : S.normOK z_i then
      .success { from    := retryState.base.share.pid,
                 session := retryState.base.session,
                 z_i     := z_i }
    else
      .retry

/-- Initialize retry state for first attempt -/
def initRetryState
  (S : Scheme)
  (st : SignLocalState S)
  (c : S.Challenge)
  : SignRetryState S :=
  { base := st, attempt := 1, challenge := c }

/-- Advance retry state with fresh nonce for next attempt.
    In practice, the fresh nonce would be sampled externally. -/
def advanceRetryState
  (S : Scheme)
  (retryState : SignRetryState S)
  (freshNonce : S.Secret)
  (freshW : S.Public)
  (freshOpen : S.Opening)
  : SignRetryState S :=
  { retryState with
    base := { retryState.base with
              y_i := freshNonce
              w_i := freshW
              openW := freshOpen }
    attempt := retryState.attempt + 1 }

/-- Check if we should abort due to too many retries -/
def shouldAbort (S : Scheme) (retryState : SignRetryState S) : Bool :=
  retryState.attempt > maxSigningAttempts

/-- Predicate: signing eventually succeeds or aborts (no infinite loop) -/
def signingTerminates (S : Scheme) (retryState : SignRetryState S) : Prop :=
  retryState.attempt ≤ maxSigningAttempts + 1

/-!
## Signature Aggregation

Combine partial signatures into final signature.
- n-of-n: simple sum z = Σ z_i
- t-of-n: weighted sum z = Σ λ_i·z_i via Lagrange
-/

/-- Final signature: z, challenge c, signer set, commitments. -/
structure Signature (S : Scheme) :=
  (z       : S.Secret)           -- aggregated signature value
  (c       : S.Challenge)        -- Fiat-Shamir challenge
  (Sset    : List S.PartyId)     -- signers who participated
  (commits : List S.Commitment)  -- commitments (for verification)
deriving Repr

/-!
## Aggregation Strategies

We unify n-of-n and t-of-n aggregation under a single strategy abstraction.
When the coefficients are all 1 (the all-parties case), we take the cheap
additive path with no inverses. When supplied with Lagrange coefficients, we
take the weighted path. Validation makes sure coefficients align with the
active set and share list to avoid misuse.
-/

/-- Simple n-of-n aggregation: z = Σ z_i. -/
def aggregateSignature
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  : Signature S :=
  let z : S.Secret := (shares.map (·.z_i)).sum
  { z := z, c := c, Sset := Sset, commits := commits }

/-- Weighted aggregation: z = Σ λ_i·z_i via provided coefficients. -/
def aggregateSignatureLagrange
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (coeffs : List (LagrangeCoeff S))
  (shares : List (SignShareMsg S))
  : Signature S :=
  let z : S.Secret :=
    (List.zipWith (fun coeff sh => coeff.lambda • sh.z_i) coeffs shares).sum
  { z := z, c := c, Sset := Sset, commits := commits }

/-!
### Unified Strategy

CoeffStrategy selects how partials are combined:
- ones: simple sum z = Σ z_i (n-of-n, no field ops needed)
- lagrange: weighted sum z = Σ λ_i·z_i (t-of-n, requires field)
-/

/-- Coefficient strategy: how to combine partial signatures. -/
inductive CoeffStrategy (S : Scheme)
  | ones                                      -- n-of-n: z = Σ z_i
  | lagrange (coeffs : List (LagrangeCoeff S)) -- t-of-n: z = Σ λ_i·z_i

/-- Validity predicate: coefficients align with active signer list.
    Prevents length/ordering mismatches during zipWith. -/
def strategyOK (S : Scheme) [DecidableEq S.PartyId]
  (active : List S.PartyId) : CoeffStrategy S → Prop
  | .ones => True
  | .lagrange coeffs =>
      coeffs.length = active.length ∧ coeffs.map (·.pid) = active

/-- Aggregate using strategy, validating shares against active set.
    Returns none on membership or length failures. -/
def aggregateWithStrategy
  (S    : Scheme) [DecidableEq S.PartyId]
  (c    : S.Challenge)
  (active : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  (strategy : CoeffStrategy S)
  : Option (Signature S) :=
  -- Membership check: all shares from declared active set
  if hfrom : ∀ sh ∈ shares, sh.sender ∈ active then
    match strategy with
    | .ones =>
        -- n-of-n path: just need length match
        if hlen : shares.length = active.length then
          some (aggregateSignature S c active commits shares)
        else none
    | .lagrange coeffs =>
        -- t-of-n path: coeffs must align with shares
        if hlen : shares.length = coeffs.length then
          if hpid : coeffs.map (·.pid) = active then
            some (aggregateSignatureLagrange S c active commits coeffs shares)
          else none
        else none
  else none

/-!
## Transcript Validation

Full validation of signing transcript before aggregation.
Checks lengths, sessions, commitments, and participants.
-/

/-- Validate transcript and produce signature if valid.
    Returns specific error on failure for debugging. -/
def validateSigning
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  : Except (SignError S.PartyId) (Signature S) := do
  -- Check message counts match
  if hlen : commits.length = reveals.length ∧ reveals.length = shares.length then pure () else
    throw .lengthMismatch
  let sess := (commits.headD (by cases commits <;> simp)).session
  let pids := commits.map (·.sender)
  -- Check no duplicate signers
  if hdup : pids.Nodup then pure () else throw (.duplicateParticipants (pids.headD (by cases pids <;> simp)))
  -- Check signers match expected set
  if hpids : pids = Sset then pure () else throw (.participantMismatch (pids.headD (by cases pids <;> simp)))
  -- Verify each commitment opens correctly
  for (c,r) in List.zip commits reveals do
    if hpid : c.sender = r.sender then
      if hcom : S.commit r.w_i r.opening = c.commitW then
        if hsess : r.session = sess then pure ()
        else throw (.sessionMismatch sess r.session)
      else throw (.commitMismatch r.sender)
    else throw (.participantMismatch c.sender)
  -- Check all shares have same session
  for sh in shares do
    if hsess : sh.session = sess then pure () else throw (.sessionMismatch sess sh.session)
  -- Compute challenge and aggregate
  let w : S.Public := (reveals.map (·.w_i)).sum
  let c : S.Challenge := S.hash m pk Sset (commits.map (·.commitW)) w
  let sig := aggregateSignature S c Sset (commits.map (·.commitW)) shares
  pure sig

/-!
## Threshold Context

ThresholdCtx bundles:
- active: the Finset of participating signers
- t: the threshold (min signers needed)
- mode: all-parties vs general threshold
- strategy: how to aggregate (ones vs lagrange)
- proofs: t ≤ |active| and strategy alignment

This allows the protocol to choose the efficient path (simple sum) when
possible, while maintaining invariants needed for correctness.
-/

/-- Signing mode: all-parties (n-of-n) or general threshold (t-of-n). -/
inductive SignMode | all | threshold
deriving DecidableEq

/-- Threshold context with proofs of well-formedness.
    Carries both configuration and validity guarantees. -/
structure ThresholdCtx (S : Scheme) [DecidableEq S.PartyId] :=
  (active     : Finset S.PartyId)    -- participating signers
  (t          : Nat)                 -- threshold (t = |active| for n-of-n)
  (mode       : SignMode)            -- n-of-n vs t-of-n
  (strategy   : CoeffStrategy S)     -- aggregation method
  (card_ge    : t ≤ active.card)     -- proof: have enough signers
  (strategy_ok : strategyOK S active.toList strategy) -- coeffs align
deriving Repr

/-- Membership predicate: all shares from declared active set. -/
def sharesFromActive (S : Scheme) [DecidableEq S.PartyId]
  (ctx : ThresholdCtx S) (shares : List (SignShareMsg S)) : Prop :=
  ∀ sh ∈ shares, sh.sender ∈ ctx.active

/-- Decidable instance for sharesFromActive. -/
instance sharesFromActiveDecidable (S : Scheme) [DecidableEq S.PartyId]
  (ctx : ThresholdCtx S) (shares : List (SignShareMsg S))
  : Decidable (sharesFromActive S ctx shares) :=
  List.decidableBAll shares (fun sh => sh.sender ∈ ctx.active)

/-!
### Context Constructors

Smart constructors build ThresholdCtx with proofs:
- mkAllCtx: for n-of-n (all parties sign)
- mkThresholdCtx: for t-of-n with pre-supplied coefficients
- mkThresholdCtxComputed: recomputes Lagrange coeffs from active set
-/

/-- Build n-of-n context: threshold = |active|, strategy = ones. -/
def mkAllCtx (S : Scheme) [DecidableEq S.PartyId]
  (active : Finset S.PartyId) : ThresholdCtx S :=
{ active := active,
  t := active.card,
  mode := SignMode.all,
  strategy := CoeffStrategy.ones,
  card_ge := by simp,
  strategy_ok := by trivial }

/-- Build t-of-n context with pre-supplied Lagrange coefficients.
    Caller provides proofs that coeffs align with active set. -/
def mkThresholdCtx
  (S : Scheme) [DecidableEq S.PartyId]
  (active : Finset S.PartyId)
  (t : Nat)
  (coeffs : List (LagrangeCoeff S))
  (hcard : t ≤ active.card)
  (halign : coeffs.map (·.pid) = active.toList)
  (hlen : coeffs.length = active.toList.length)
  : ThresholdCtx S :=
{ active := active,
  t := t,
  mode := SignMode.threshold,
  strategy := CoeffStrategy.lagrange coeffs,
  card_ge := hcard,
  strategy_ok := by simp [strategyOK, halign, hlen] }

/-- Extract Lagrange coefficients from existing context.
    Recomputes λ_i for each party in active set. -/
noncomputable def coeffsFromCtx
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (ctx : ThresholdCtx S)
  (pidToScalar : S.PartyId → S.Scalar) : List (LagrangeCoeff S) :=
  ctx.active.toList.map (fun pid =>
    { pid := pid, lambda := lagrangeCoeffAtZero S pidToScalar ctx.active.toList pid })

/-- Build t-of-n context by computing fresh Lagrange coefficients.
    Requires Field for division in Lagrange formula. -/
noncomputable def mkThresholdCtxComputed
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (active : Finset S.PartyId)
  (t : Nat)
  (pidToScalar : S.PartyId → S.Scalar)
  (hcard : t ≤ active.card) : ThresholdCtx S :=
  let coeffs := active.toList.map (fun pid =>
    { pid := pid, lambda := lagrangeCoeffAtZero S pidToScalar active.toList pid })
  have hlen : coeffs.length = active.toList.length := by simp
  have hpid : coeffs.map (·.pid) = active.toList := by
    simp only [List.map_map, Function.comp]
    exact List.map_id _
  mkThresholdCtx S active t coeffs hcard hpid hlen

/-- Refresh context with fresh coefficients (same active set/threshold). -/
noncomputable def refreshThresholdCtx
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (pidToScalar : S.PartyId → S.Scalar)
  (ctx : ThresholdCtx S) : ThresholdCtx S :=
  mkThresholdCtxComputed S ctx.active ctx.t pidToScalar ctx.card_ge

/-!
### Context-Based Aggregation

These functions use ThresholdCtx to select the right aggregation path
and validate shares against the declared active set.
-/

/-- Aggregate using context's strategy after membership validation.
    Returns none if shares aren't from active set. -/
noncomputable def aggregateSignatureWithCtx
  (S    : Scheme) [DecidableEq S.PartyId]
  (c    : S.Challenge)
  (ctx  : ThresholdCtx S)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  : Option (Signature S) :=
  if _hfrom : sharesFromActive S ctx shares then
    aggregateWithStrategy S c ctx.active.toList commits shares ctx.strategy
  else
    none

/-- Direct Lagrange aggregation using context's active set.
    Assumes coeffs are already validated. -/
noncomputable def aggregateSignatureLagrangeThresh
  (S    : Scheme) [DecidableEq S.PartyId]
  (c    : S.Challenge)
  (ctx  : ThresholdCtx S)
  (commits : List S.Commitment)
  (coeffs : List (LagrangeCoeff S))
  (shares : List (SignShareMsg S))
  : Signature S :=
  aggregateSignatureLagrange S c ctx.active.toList commits coeffs shares

/-!
## CRDT Pipeline Output

SignatureDone wraps the final signature for the CRDT pipeline.
Indicates signing protocol reached completion.
-/

/-- Final signature wrapper for CRDT done state. -/
structure SignatureDone (S : Scheme) where
  sig : Signature S
deriving Repr

end IceNine.Protocol
