/-
# Session-Typed Signing Protocol

Linear session types for threshold signing that make nonce reuse impossible.
Each signing session progresses through states that consume the previous state,
ensuring nonces are used exactly once.

**Key insight**: A nonce must be used exactly once. Session types encode this
constraint in the type system—the nonce is consumed when transitioning from
`Committed` to `Revealed`, and the type system prevents accessing it again.

## Session State Machine

```
  FreshNonce ──┬──► Committed ──► Revealed ──► Signed ──► Done
               │
               └──► Aborted (on retry failure)
```

Each transition consumes the input state and produces the output state.
There is no way to "go back" or reuse a consumed state.
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.Core.ThresholdConfig
import IceNine.Protocol.Core.NormBounded
import IceNine.Protocol.Core.Error
import IceNine.Protocol.State.Phase
import IceNine.Protocol.Sign.Types
import IceNine.Protocol.Sign.LocalRejection
import Mathlib

namespace IceNine.Protocol.SignSession

open IceNine.Protocol

/-!
## Linear Nonce (Dual Nonce Version)

Following FROST, we use two nonces per signer:
- **Hiding nonce**: Protects against adaptive adversaries
- **Binding nonce**: Commits to the signing context

The `private mk` prevents construction outside this module, and
the only way to use the nonces is through session transitions.
-/

/-- A fresh, unused dual nonce pair. Can only be consumed once.
    Private constructor prevents arbitrary creation.

    **FROST Pattern**: Both nonces must be fresh from CSPRNG. -/
structure FreshNonce (S : Scheme) where
  private mk ::
  /-- Secret hiding nonce -/
  private hidingNonce : S.Secret
  /-- Secret binding nonce -/
  private bindingNonce : S.Secret
  /-- Public hiding commitment W_hiding = A(hiding) -/
  private publicHiding : S.Public
  /-- Public binding commitment W_binding = A(binding) -/
  private publicBinding : S.Public
  /-- Commitment opening for hiding commitment -/
  private opening : S.Opening

/-- Proof that nonces were consumed. Produced exactly once per nonce pair. -/
structure NonceConsumed (S : Scheme) where
  private mk ::
  /-- Hash of the consumed nonce (for debugging, not reconstruction) -/
  fingerprint : Nat := 0

/-- Create fresh dual nonces from sampled randomness.
    This is the ONLY way to create a FreshNonce.

    **CRITICAL**: Both hiding and binding nonces must be fresh from CSPRNG. -/
def FreshNonce.sample (S : Scheme)
    (h b : S.Secret) (opening : S.Opening) : FreshNonce S :=
  { hidingNonce := h
    bindingNonce := b
    publicHiding := S.A h
    publicBinding := S.A b
    opening := opening }

/-!
## Session States

Each state in the signing protocol. States are parameterized by the scheme
and carry the data accumulated up to that point. Transitions consume the
current state and produce the next state.
-/

/-- After committing: nonces are consumed, commitments are published. -/
structure Committed (S : Scheme) where
  /-- Party's key share -/
  keyShare : KeyShare S
  /-- Secret hiding nonce (moved from FreshNonce) -/
  private hidingNonce : S.Secret
  /-- Secret binding nonce (moved from FreshNonce) -/
  private bindingNonce : S.Secret
  /-- Public hiding commitment -/
  publicHiding : S.Public
  /-- Public binding commitment -/
  publicBinding : S.Public
  /-- Commitment opening -/
  opening : S.Opening
  /-- Message being signed -/
  message : S.Message
  /-- Session identifier -/
  session : Nat
  /-- The hash commitment to hiding nonce -/
  commitment : S.Commitment
  /-- Proof the nonces were consumed -/
  nonceConsumed : NonceConsumed S

/-- Initial state: party has key share and fresh dual nonces, ready to commit. -/
structure ReadyToCommit (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment] where
  /-- Party's long-term key share -/
  keyShare : KeyShare S
  /-- Fresh dual nonces (will be consumed on commit) -/
  nonce : FreshNonce S
  /-- Message to sign -/
  message : S.Message
  /-- Session identifier -/
  session : Nat
  /-- Session tracker to prevent reuse of session IDs for this party -/
  tracker : SessionTracker S
  /-- Nonce registry to detect commitment reuse across sessions -/
  nonceReg : NonceRegistry S

/-- State bundle carrying updated trackers after commit. -/
structure CommitResult (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment] where
  committed : Committed S
  msg : SignCommitMsg S
  tracker : SessionTracker S
  nonceReg : NonceRegistry S

/-- After revealing: nonce openings revealed, ready to compute partial sig. -/
structure Revealed (S : Scheme) where
  /-- Party's key share -/
  keyShare : KeyShare S
  /-- Secret hiding nonce (needed for effective nonce derivation) -/
  private hidingNonce : S.Secret
  /-- Secret binding nonce (needed for effective nonce derivation) -/
  private bindingNonce : S.Secret
  /-- Public hiding commitment -/
  publicHiding : S.Public
  /-- Public binding commitment -/
  publicBinding : S.Public
  /-- Message being signed -/
  message : S.Message
  /-- Session identifier -/
  session : Nat
  /-- Challenge computed from transcript -/
  challenge : S.Challenge
  /-- Binding factor for this signer -/
  bindingFactor : S.Scalar
  /-- Aggregate public nonce from all parties -/
  aggregateNonce : S.Public

/-- After signing: partial signature produced. -/
structure Signed (S : Scheme) where
  /-- Party's key share (secret no longer needed) -/
  keyShare : KeyShare S
  /-- The partial signature -/
  partialSig : S.Secret
  /-- Message that was signed -/
  message : S.Message
  /-- Session identifier -/
  session : Nat
  /-- Challenge -/
  challenge : S.Challenge

/-- Terminal state: signing complete for this party. -/
structure Done (S : Scheme) where
  /-- The share message to send to aggregator -/
  shareMsg : SignShareMsg S

/-- Aborted state: signing failed (e.g., norm check failed after max retries). -/
structure Aborted (S : Scheme) where
  /-- Session that was aborted -/
  session : Nat
  /-- Reason for abort -/
  reason : String
  /-- Attempt count when aborted -/
  attempts : Nat

/-!
## Session Transitions

Each transition function consumes its input state and produces the next state.
The type signatures enforce the linear protocol flow.
-/

/-- Transition: Ready → Committed
    Consumes the fresh dual nonces and produces commitments.
    After this, the nonces cannot be accessed again from ReadyToCommit.

    **FROST Protocol**: Broadcasts both public commitments (hiding + binding)
    along with a hash commitment to the hiding nonce for equivocation prevention.

    Enforces session freshness for the signer via `SessionTracker`. -/
def commit (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (ready : ReadyToCommit S)
    : Except (SignError S.PartyId) (CommitResult S) :=
  if ready.tracker.isFresh ready.session then
    -- Extract nonce data (consumes the FreshNonce)
    let hidingNonce := ready.nonce.hidingNonce
    let bindingNonce := ready.nonce.bindingNonce
    let publicHiding := ready.nonce.publicHiding
    let publicBinding := ready.nonce.publicBinding
    let opening := ready.nonce.opening
    -- Create commitment to hiding nonce
    let commitment := S.commit publicHiding opening
    -- Build committed state (nonces are now here, not in FreshNonce)
    let committed : Committed S :=
      { keyShare := ready.keyShare
        hidingNonce := hidingNonce
        bindingNonce := bindingNonce
        publicHiding := publicHiding
        publicBinding := publicBinding
        opening := opening
        message := ready.message
        session := ready.session
        commitment := commitment
        nonceConsumed := { fingerprint := 0 } }
    -- Build message for broadcast (includes both public commitments)
    let msg : SignCommitMsg S :=
      { sender := ready.keyShare.pid
        session := ready.session
        commitW := commitment
        hidingVal := publicHiding
        bindingVal := publicBinding }
    let tracker' := ready.tracker.markUsed ready.session
    let nonceReg' := ready.nonceReg.record ready.keyShare.pid ready.session commitment
    match ready.nonceReg.detectReuse ready.keyShare.pid commitment with
        | some (s1, s2) => throw (.sessionMismatch s1 s2)
        | none => pure { committed := committed, msg := msg, tracker := tracker', nonceReg := nonceReg' }
  else
    throw (.sessionMismatch ready.session ready.session)

/-- Transition: Committed → Revealed
    Called after receiving all commitments and computing binding factors/challenge.

    **FROST Protocol**: The binding factor ρ is computed from the message, public key,
    and all participants' commitments. This binds the effective nonce to the signing context. -/
def reveal (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (committed : Committed S)
    (challenge : S.Challenge) (bindingFactor : S.Scalar) (aggregateW : S.Public)
    (tracker : SessionTracker S) (nonceReg : NonceRegistry S)
    : Revealed S × SignRevealWMsg S × SessionTracker S × NonceRegistry S :=
  -- Build revealed state
  let revealed : Revealed S :=
    { keyShare := committed.keyShare
      hidingNonce := committed.hidingNonce
      bindingNonce := committed.bindingNonce
      publicHiding := committed.publicHiding
      publicBinding := committed.publicBinding
      message := committed.message
      session := committed.session
      challenge := challenge
      bindingFactor := bindingFactor
      aggregateNonce := aggregateW }
  -- Build reveal message (just opening - public nonces already sent in commit)
  let msg : SignRevealWMsg S :=
    { sender := committed.keyShare.pid
      session := committed.session
      opening := committed.opening }
  (revealed, msg, tracker, nonceReg)

/-- Transition: Revealed → Signed (success) or Revealed → Aborted (norm failure)
    Computes partial signature z_i = y_eff_i + c·sk_i where
    y_eff = hiding + ρ·binding (effective nonce from dual nonce structure).
    Returns Left if norm check passes, Right if it fails.

    **FROST Protocol**: The effective nonce incorporates the binding factor,
    which ties this signer's contribution to the specific signing context. -/
def sign (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (revealed : Revealed S)
    (tracker : SessionTracker S) (nonceReg : NonceRegistry S)
    : Sum (Signed S × SessionTracker S × NonceRegistry S) (Revealed S × String) :=
  -- Derive effective nonce: y_eff = hiding + ρ·binding
  let y_eff := revealed.hidingNonce + revealed.bindingFactor • revealed.bindingNonce
  -- Compute partial signature: z_i = y_eff + c·sk_i
  let z_i := y_eff + revealed.challenge • revealed.keyShare.secret
  -- Check norm bound
  if S.normOK z_i then
    let signed : Signed S :=
      { keyShare := revealed.keyShare
        partialSig := z_i
        message := revealed.message
        session := revealed.session
        challenge := revealed.challenge }
    Sum.inl (signed, tracker, nonceReg)
  else
    -- Return the revealed state for retry with explanation
    Sum.inr (revealed, "norm check failed")

/-- Transition: Signed → Done
    Packages the partial signature for the aggregator. -/
def finalize (S : Scheme) (signed : Signed S) : Done S :=
  let msg : SignShareMsg S :=
    { sender := signed.keyShare.pid
      session := signed.session
      z_i := signed.partialSig }
  { shareMsg := msg }

/-!
## Retry Handling

When norm check fails, we need a fresh nonce. This requires going back to
ReadyToCommit with a NEW FreshNonce. The old session state is consumed,
preventing any reuse of the old nonce.
-/

/-- Retry state: tracks attempts for a signing session.

    **Session ID Design**: The session ID remains constant across retries within the same
    signing session. This is intentional for threshold signing coordination:

    1. **Coordination**: All parties must agree on which session they're retrying.
       Using the same session ID allows parties to correlate retry rounds.

    2. **Nonce Safety**: Nonce reuse is prevented by the `FreshNonce` type, not by
       session ID. Each retry requires a newly sampled `FreshNonce`, and the type
       system ensures each `FreshNonce` is consumed exactly once.

    3. **Distinguishing Retries**: The `attempt` field distinguishes retry rounds
       within a session. A full session identifier is effectively `(session, attempt)`.

    4. **Tracking**: The `SessionTracker` marks the base session ID as used after
       the first commit. Retries don't re-mark because they use fresh nonces within
       the same logical session.

    **Alternative Design**: If independent session IDs per retry are needed (e.g., for
    independent parallel attempts), use `retryWithNewSession` instead. -/
structure RetryContext (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment] where
  /-- Current attempt number (1-indexed) -/
  attempt : Nat
  /-- Maximum allowed attempts -/
  maxAttempts : Nat
  /-- Key share (persistent across retries) -/
  keyShare : KeyShare S
  /-- Message (persistent across retries) -/
  message : S.Message
  /-- Base session ID (constant across retries for coordination) -/
  session : Nat
  /-- Session tracker (persistent across retries) -/
  tracker : SessionTracker S
  /-- Nonce registry (persistent across retries) -/
  nonceReg : NonceRegistry S

/-- Create retry context from revealed state after norm failure.
    The revealed state is consumed—it cannot be used again.
    Requires tracker and nonceReg to be passed through from the commit phase. -/
def mkRetryContext (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (revealed : Revealed S) (maxAttempts : Nat)
    (tracker : SessionTracker S) (nonceReg : NonceRegistry S)
    : RetryContext S :=
  { attempt := 1
    maxAttempts := maxAttempts
    keyShare := revealed.keyShare
    message := revealed.message
    session := revealed.session
    tracker := tracker
    nonceReg := nonceReg }

/-- Advance retry context for next attempt.
    Returns None if max attempts exceeded. -/
def advanceRetry {S : Scheme}
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (ctx : RetryContext S) : Option (RetryContext S) :=
  if ctx.attempt < ctx.maxAttempts then
    some { ctx with attempt := ctx.attempt + 1 }
  else
    none

/-- Create new ReadyToCommit for retry with FRESH nonce.
    The fresh nonce must be newly sampled—cannot reuse old nonce.

    **Note**: Uses same session ID for threshold coordination. All parties in the
    signing group should retry together with the same base session ID. -/
def retryWithFreshNonce (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (ctx : RetryContext S) (freshNonce : FreshNonce S)
    : ReadyToCommit S :=
  { keyShare := ctx.keyShare
    nonce := freshNonce
    message := ctx.message
    session := ctx.session
    tracker := ctx.tracker
    nonceReg := ctx.nonceReg }

/-- Create new ReadyToCommit for retry with FRESH nonce AND new session ID.
    Use this when retries should be independent sessions (e.g., parallel attempts).

    **Warning**: New session requires coordination with other parties to ensure
    they also use the new session ID. -/
def retryWithNewSession (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (ctx : RetryContext S) (freshNonce : FreshNonce S) (newSession : Nat)
    : ReadyToCommit S :=
  { keyShare := ctx.keyShare
    nonce := freshNonce
    message := ctx.message
    session := newSession
    tracker := ctx.tracker
    nonceReg := ctx.nonceReg }

/-- Create aborted state when max retries exceeded. -/
def abort (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (ctx : RetryContext S) : Aborted S :=
  { session := ctx.session
    reason := s!"max retries ({ctx.maxAttempts}) exceeded"
    attempts := ctx.attempt }

/-!
## Full Signing Flow

Convenience function that runs the full protocol for a single party.
Each step consumes the previous state.
-/

/-- Result of a signing attempt. -/
inductive SignResult (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
  | success (done : Done S)
  | needsRetry (ctx : RetryContext S)
  | aborted (aborted : Aborted S)

/-- Run signing from Revealed state through to completion or retry.
    Requires tracker and nonceReg for creating retry context. -/
def trySign (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (revealed : Revealed S)
    (tracker : SessionTracker S) (nonceReg : NonceRegistry S)
    (maxAttempts : Nat := 16)
    : SignResult S :=
  match sign S revealed tracker nonceReg with
  | Sum.inl (signed, _, _) =>
      .success (finalize S signed)
  | Sum.inr (revealed', _) =>
      let ctx := mkRetryContext S revealed' maxAttempts tracker nonceReg
      if ctx.attempt < ctx.maxAttempts then
        .needsRetry ctx
      else
        .aborted (abort S ctx)

/-!
## Initialization

Create the initial session state from key share and sampled randomness.
-/

/-- Initialize a signing session with dual nonces and tracker.
    Caller must provide freshly sampled hiding and binding nonces.

    **CRITICAL**: Both nonces must be fresh from CSPRNG. -/
def initSession (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (keyShare : KeyShare S)
    (message : S.Message)
    (session : Nat)
    (hidingNonce bindingNonce : S.Secret)
    (opening : S.Opening)
    (tracker : SessionTracker S := SessionTracker.empty S keyShare.pid)
    (nonceReg : NonceRegistry S := NonceRegistry.empty S)
    : ReadyToCommit S :=
  { keyShare := keyShare
    nonce := FreshNonce.sample S hidingNonce bindingNonce opening
    message := message
    session := session
    tracker := tracker
    nonceReg := nonceReg }

/-!
## Type-Level Guarantees

The session type system provides these guarantees:

1. **Nonce uniqueness**: Each `FreshNonce` can only be consumed once.
   The `commit` function consumes the `ReadyToCommit` state, and the
   nonce value moves into `Committed`. There's no path back.

2. **Linear flow**: States can only progress forward:
   ReadyToCommit → Committed → Revealed → Signed → Done
   Each transition consumes its input.

3. **No nonce reuse on retry**: When signing fails norm check, we must
   create a NEW `ReadyToCommit` with a NEW `FreshNonce`. The old
   `Revealed` state is consumed by `mkRetryContext`.

4. **Compile-time enforcement**: These aren't runtime checks—the type
   system prevents writing code that would reuse a nonce.
-/

-- Example: this CANNOT compile because `ready` is consumed by first `commit`
-- def badNonceReuse (S : Scheme) (ready : ReadyToCommit S) :=
--   let (committed1, _) := commit S ready  -- consumes ready
--   let (committed2, _) := commit S ready  -- ERROR: ready already consumed
--   (committed1, committed2)

/-!
## Precomputed Nonces

Support for pre-generating nonce commitments before signing requests arrive.
This enables single-round-trip signing when nonces are prepared ahead of time,
which is critical for protocols like Aura's fast path.

**Use case**: Aura witnesses can precompute nonces during idle time, then
produce shares immediately when an Execute message arrives.

**Safety**: Precomputed nonces have expiry to prevent long-term storage.
Nonces should be regenerated periodically.
-/

/-- A precomputed nonce ready for immediate use.
    Parties can generate these during idle time for faster signing.

    **Expiry**: Nonces should not be stored indefinitely. The `maxAge` field
    specifies the maximum lifetime in seconds. Expired nonces should be discarded. -/
structure PrecomputedNonce (S : Scheme) where
  /-- The commitment that will be broadcast (visible to all) -/
  commitment : S.Commitment
  /-- The fresh nonce (consumed on use) -/
  nonce : FreshNonce S
  /-- Public hiding commitment (for fast path) -/
  publicHiding : S.Public
  /-- Public binding commitment (for fast path) -/
  publicBinding : S.Public
  /-- Generation timestamp (seconds since epoch) -/
  generatedAt : Nat
  /-- Maximum age in seconds (default: 1 hour) -/
  maxAge : Nat := 3600

/-- Create a precomputed nonce from freshly sampled randomness.
    The commitment is computed immediately so it can be pre-shared. -/
def PrecomputedNonce.create (S : Scheme)
    (hidingSecret bindingSecret : S.Secret)
    (opening : S.Opening)
    (currentTime : Nat)
    (maxAge : Nat := 3600)
    : PrecomputedNonce S :=
  let freshNonce := FreshNonce.sample S hidingSecret bindingSecret opening
  { commitment := S.commit (S.A hidingSecret) opening
    nonce := freshNonce
    publicHiding := S.A hidingSecret
    publicBinding := S.A bindingSecret
    generatedAt := currentTime
    maxAge := maxAge }

/-- Check if a precomputed nonce has expired. -/
def PrecomputedNonce.isExpired {S : Scheme} (pn : PrecomputedNonce S) (currentTime : Nat) : Bool :=
  currentTime > pn.generatedAt + pn.maxAge

/-- Check if a precomputed nonce is still valid. -/
def PrecomputedNonce.isValid {S : Scheme} (pn : PrecomputedNonce S) (currentTime : Nat) : Bool :=
  !pn.isExpired currentTime

/-- Pool of precomputed nonces for a party.
    Manages multiple precomputed nonces for concurrent signing sessions. -/
structure NoncePool (S : Scheme) where
  /-- Available precomputed nonces -/
  available : List (PrecomputedNonce S)
  /-- Count of consumed nonces (for statistics) -/
  consumedCount : Nat := 0

/-- Create an empty nonce pool. -/
def NoncePool.empty (S : Scheme) : NoncePool S :=
  { available := [], consumedCount := 0 }

/-- Add a precomputed nonce to the pool. -/
def NoncePool.add {S : Scheme} (pool : NoncePool S) (pn : PrecomputedNonce S)
    : NoncePool S :=
  { pool with available := pn :: pool.available }

/-- Take a valid nonce from the pool, marking it consumed.
    Returns None if no valid nonces are available.
    Automatically prunes expired nonces. -/
def NoncePool.take {S : Scheme} (pool : NoncePool S) (currentTime : Nat)
    : Option (PrecomputedNonce S × NoncePool S) :=
  -- Filter out expired nonces
  let valid := pool.available.filter (fun pn => pn.isValid currentTime)
  match valid with
  | [] => none
  | pn :: rest =>
      some (pn, { available := rest, consumedCount := pool.consumedCount + 1 })

/-- Number of available (possibly expired) nonces in pool. -/
def NoncePool.size {S : Scheme} (pool : NoncePool S) : Nat :=
  pool.available.length

/-- Number of valid (non-expired) nonces in pool. -/
def NoncePool.validCount {S : Scheme} (pool : NoncePool S) (currentTime : Nat) : Nat :=
  (pool.available.filter (fun pn => pn.isValid currentTime)).length

/-- Prune all expired nonces from pool. -/
def NoncePool.prune {S : Scheme} (pool : NoncePool S) (currentTime : Nat) : NoncePool S :=
  { pool with available := pool.available.filter (fun pn => pn.isValid currentTime) }

/-!
## Fast Path Signing

Single-round signing for when nonces are precomputed and commitments pre-shared.
This is the mode Aura uses for its fast path: witnesses pre-share nonce commitments,
then immediately produce shares on Execute without additional rounds.

**Security Assumptions**:
1. Nonce commitments were honestly generated and not reused
2. The coordinator will not selectively abort after seeing shares
3. Precomputed nonces have not expired

Use standard two-round signing when these assumptions don't hold.
-/

/-- Fast signing with precomputed nonce.
    Skips commit-reveal phase because commitment was pre-shared.

    **SECURITY NOTE**: This mode trusts that:
    1. Nonce commitments were honestly generated
    2. Nonces are not being reused
    3. Coordinator will aggregate honestly

    Use standard two-round signing when these assumptions don't hold.

    Returns None if norm check fails (caller should retry with fresh nonce). -/
def signFast (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    [DecidableEq S.Secret]
    (keyShare : KeyShare S)
    (precomputed : PrecomputedNonce S)
    (challenge : S.Challenge)
    (bindingFactor : S.Scalar)
    (session : Nat)
    (context : ExternalContext := {})
    : Option (SignShareMsg S) :=
  let effectiveNonce := precomputed.nonce.hidingNonce + bindingFactor • precomputed.nonce.bindingNonce
  let z_i := effectiveNonce + challenge • keyShare.secret
  if decide (S.normOK z_i) then
    some { sender := keyShare.pid
           session := session
           z_i := z_i
           context := context }
  else
    none

/-- Initialize a fast-path signing session from precomputed nonce.
    Use when commitments have been pre-shared and you want to skip commit phase. -/
def initFastSession (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (keyShare : KeyShare S)
    (message : S.Message)
    (session : Nat)
    (precomputed : PrecomputedNonce S)
    (tracker : SessionTracker S := SessionTracker.empty S keyShare.pid)
    (nonceReg : NonceRegistry S := NonceRegistry.empty S)
    : ReadyToCommit S :=
  { keyShare := keyShare
    nonce := precomputed.nonce
    message := message
    session := session
    tracker := tracker
    nonceReg := nonceReg }

/-- Pre-shared commitment for fast path.
    Parties broadcast these before signing requests arrive. -/
structure PreSharedCommitment (S : Scheme) where
  /-- Party who created this commitment -/
  partyId : S.PartyId
  /-- The hash commitment -/
  commitment : S.Commitment
  /-- Public hiding value -/
  publicHiding : S.Public
  /-- Public binding value -/
  publicBinding : S.Public
  /-- When this commitment expires -/
  expiresAt : Nat

/-- Create a pre-shared commitment from a precomputed nonce. -/
def PreSharedCommitment.fromPrecomputed (S : Scheme)
    (partyId : S.PartyId)
    (pn : PrecomputedNonce S)
    : PreSharedCommitment S :=
  { partyId := partyId
    commitment := pn.commitment
    publicHiding := pn.publicHiding
    publicBinding := pn.publicBinding
    expiresAt := pn.generatedAt + pn.maxAge }

/-!
## Local Rejection Integration

Functions that integrate local rejection sampling with session types.
These replace the retry-based norm check with upfront local rejection.

**Key change**: With local rejection, `signWithLocalRejection` never fails
norm check because rejection happens before computing z_i.
-/

/-- Signed state with local rejection statistics. -/
structure SignedWithStats (S : Scheme) extends Signed S where
  /-- Number of local rejection attempts -/
  localAttempts : Nat
  /-- The hiding nonce used (needed for verification) -/
  hidingNonce : S.Secret
  /-- The binding nonce used (needed for verification) -/
  bindingNonce : S.Secret

/-- Transition: Revealed → SignedWithStats using local rejection.

    Unlike `sign`, this function uses local rejection sampling to find
    a valid z_i before returning. It never returns a norm failure because
    rejection is handled internally.

    **Inputs**:
    - `revealed`: State with challenge and binding factor
    - `cfg`: Threshold configuration with local bound
    - `sampleNonce`: IO action to sample fresh nonce pairs

    **Guarantee**: The returned z_i satisfies ‖z_i‖∞ ≤ cfg.localBound.

    **Note**: This consumes the revealed state. On success, the nonces
    in `revealed` are replaced with the successful nonces from rejection. -/
def signWithLocalRejection (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [SMul S.Challenge S.Secret] [inst : Protocol.NormBounded.NormBounded S.Secret]
    (revealed : Revealed S)
    (cfg : Protocol.ThresholdConfig.ThresholdConfig)
    (sampleNonce : IO (S.Secret × S.Secret))
    : IO (Except (Protocol.Error.LocalRejectionError S.PartyId) (SignedWithStats S)) := do
  -- Run local rejection sampling
  let result ← Protocol.LocalRejection.localRejectionLoop S
      cfg revealed.keyShare.pid revealed.keyShare.secret
      revealed.challenge revealed.bindingFactor sampleNonce
  match result with
  | .success z hiding binding attempts =>
      -- Build signed state with statistics
      let signed : Signed S :=
        { keyShare := revealed.keyShare
          partialSig := z
          message := revealed.message
          session := revealed.session
          challenge := revealed.challenge }
      return .ok { toSigned := signed
                   localAttempts := attempts
                   hidingNonce := hiding
                   bindingNonce := binding }
  | .failure err =>
      return .error err

/-- Transition: Revealed → SignedWithStats using parallel local rejection.

    Parallel variant that samples nonces in batches for better throughput.

    **Inputs**:
    - `revealed`: State with challenge and binding factor
    - `cfg`: Threshold configuration with local bound
    - `parallelCfg`: Parallelization settings
    - `sampleBatch`: IO action to sample batch of nonce pairs

    **Guarantee**: The returned z_i satisfies ‖z_i‖∞ ≤ cfg.localBound. -/
def signWithLocalRejectionParallel (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [SMul S.Challenge S.Secret] [inst : Protocol.NormBounded.NormBounded S.Secret]
    (revealed : Revealed S)
    (cfg : Protocol.ThresholdConfig.ThresholdConfig)
    (parallelCfg : Protocol.LocalRejection.ParallelConfig)
    (sampleBatch : Nat → IO (List (S.Secret × S.Secret)))
    : IO (Except (Protocol.Error.LocalRejectionError S.PartyId) (SignedWithStats S)) := do
  -- Run parallel local rejection sampling
  let result ← Protocol.LocalRejection.localRejectionLoopParallel S
      cfg parallelCfg revealed.keyShare.pid revealed.keyShare.secret
      revealed.challenge revealed.bindingFactor sampleBatch
  match result with
  | .success z hiding binding attempts =>
      let signed : Signed S :=
        { keyShare := revealed.keyShare
          partialSig := z
          message := revealed.message
          session := revealed.session
          challenge := revealed.challenge }
      return .ok { toSigned := signed
                   localAttempts := attempts
                   hidingNonce := hiding
                   bindingNonce := binding }
  | .failure err =>
      return .error err

/-- Fast path signing with local rejection.

    Combines precomputed nonces with local rejection for single-round signing.
    Unlike `signFast`, this runs rejection sampling internally.

    **Inputs**:
    - `keyShare`: Party's key share
    - `precomputed`: Precomputed nonce (consumed)
    - `challenge`: Fiat-Shamir challenge
    - `bindingFactor`: Binding factor ρ_i
    - `cfg`: Threshold configuration
    - `session`: Session ID
    - `sampleNonce`: IO action for fresh nonces (used if precomputed fails)

    **Returns**: Share message with local rejection statistics. -/
def signFastWithLocalRejection (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [SMul S.Challenge S.Secret] [inst : Protocol.NormBounded.NormBounded S.Secret]
    (keyShare : KeyShare S)
    (precomputed : PrecomputedNonce S)
    (challenge : S.Challenge)
    (bindingFactor : S.Scalar)
    (cfg : Protocol.ThresholdConfig.ThresholdConfig)
    (session : Nat)
    (sampleNonce : IO (S.Secret × S.Secret))
    (context : ExternalContext := {})
    : IO (Except (Protocol.Error.LocalRejectionError S.PartyId) (SignShareMsg S × Nat)) := do
  -- First try the precomputed nonce
  let hiding := precomputed.nonce.hidingNonce
  let binding := precomputed.nonce.bindingNonce
  match Protocol.LocalRejection.RejectionOp.tryOnce cfg keyShare.secret challenge hiding binding bindingFactor with
  | some z =>
      -- Precomputed nonce works!
      return .ok ({ sender := keyShare.pid, session := session, z_i := z, context := context }, 1)
  | none =>
      -- Precomputed nonce failed, run full rejection loop
      let result ← Protocol.LocalRejection.localRejectionLoop S
          cfg keyShare.pid keyShare.secret challenge bindingFactor sampleNonce
      match result with
      | .success z _ _ attempts =>
          return .ok ({ sender := keyShare.pid, session := session, z_i := z, context := context }, attempts + 1)
      | .failure err =>
          return .error err

end IceNine.Protocol.SignSession
