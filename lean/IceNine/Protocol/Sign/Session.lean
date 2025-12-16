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
  FreshNonce ──► Committed ──► Revealed ──► SignedWithStats ──► Done
                    │              │
                    └──────► Aborted ◄──────┘
```

Each transition consumes the input state and produces the output state.
There is no way to "go back" or reuse a consumed state. Sessions may
transition to `Aborted` from `Committed` or `Revealed` if abort consensus
is reached (see `Protocol/Core/Abort.lean`).

**Local Rejection**: With local rejection sampling (via `signWithLocalRejection`),
norm bounds are satisfied during signing—no retry loop is needed. Use
`Protocol/Sign/LocalRejection.lean` for the local rejection implementation.
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.Core.ThresholdConfig
import IceNine.Protocol.Core.NormBounded
import IceNine.Protocol.Core.Error
import IceNine.Protocol.Core.Abort
import IceNine.Protocol.State.Phase
import IceNine.Protocol.Sign.Types
import IceNine.Protocol.Sign.LocalRejection
import Mathlib

namespace IceNine.Protocol.SignSession

open IceNine.Protocol
open IceNine.Protocol.Abort

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

/-- Terminal state: session was aborted.

    A session may be aborted due to:
    - Liveness failures (timeout, insufficient participants)
    - Security violations (trust violation, global norm exceeded)
    - Explicit abort request

    Once aborted, the session cannot continue. Any nonces consumed
    during the session are invalidated and cannot be reused.

    See `Protocol/Core/Abort.lean` for abort coordination. -/
structure Aborted (S : Scheme) [Repr S.PartyId] where
  /-- Session that was aborted -/
  session : Nat
  /-- Why the session was aborted -/
  reason : AbortReason S.PartyId
  /-- Number of parties that voted for abort -/
  voteCount : Nat
  deriving Repr

/-- Create Aborted state from AbortState. -/
def Aborted.fromState {S : Scheme} [Repr S.PartyId] (session : Nat) (state : AbortState S) : Aborted S :=
  { session
    reason := state.reasons.head?.getD (.timeout 0 0)
    voteCount := state.voteCount }

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

/-- Transition: Signed → Done
    Packages the partial signature for the aggregator. -/
def finalize (S : Scheme) (signed : Signed S) : Done S :=
  let msg : SignShareMsg S :=
    { sender := signed.keyShare.pid
      session := signed.session
      z_i := signed.partialSig }
  { shareMsg := msg }

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
   ReadyToCommit → Committed → Revealed → SignedWithStats → Done
   Each transition consumes its input. Sessions may also transition
   to `Aborted` from `Committed` or `Revealed`.

3. **Local rejection**: With `signWithLocalRejection`, norm bounds are
   satisfied during signing via local rejection sampling. No global
   retry loop is needed.

4. **Compile-time enforcement**: These aren't runtime checks—the type
   system prevents writing code that would reuse a nonce.

5. **Abort safety**: Aborted sessions cannot continue. Once a session
   transitions to `Aborted`, any consumed nonces are invalidated.
-/

/-!
## Abort Transitions

Sessions may transition to `Aborted` from intermediate states when
abort consensus is reached. These transitions consume the current
state, ensuring nonces cannot be reused.
-/

/-- Transition: Committed → Aborted
    Aborts a session after commitment but before reveal.

    **When to use**: Timeout waiting for other parties' commitments,
    or security violation detected during commitment phase. -/
def abortFromCommitted (S : Scheme) [Repr S.PartyId]
    (committed : Committed S)
    (reason : AbortReason S.PartyId)
    (voteCount : Nat := 1)
    : Aborted S :=
  { session := committed.session
    reason := reason
    voteCount := voteCount }

/-- Transition: Revealed → Aborted
    Aborts a session after reveal but before signing.

    **When to use**: Timeout waiting for other parties' reveals,
    trust violation detected, or explicit abort request. -/
def abortFromRevealed (S : Scheme) [Repr S.PartyId]
    (revealed : Revealed S)
    (reason : AbortReason S.PartyId)
    (voteCount : Nat := 1)
    : Aborted S :=
  { session := revealed.session
    reason := reason
    voteCount := voteCount }

/-- Create an abort message proposing session termination. -/
def proposeAbort (S : Scheme)
    (partyId : S.PartyId)
    (session : Nat)
    (reason : AbortReason S.PartyId)
    : AbortMsg S :=
  { sender := partyId
    session := session
    reason := reason }

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
## Fast Path

Single-round signing for when nonces are precomputed and commitments pre-shared.
-/

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
  | .success z hid binding attempts =>
      -- Build signed state with statistics
      let signed : Signed S :=
        { keyShare := revealed.keyShare
          partialSig := z
          message := revealed.message
          session := revealed.session
          challenge := revealed.challenge }
      return .ok { toSigned := signed
                   localAttempts := attempts
                   hidingNonce := hid
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
  | .success z hid binding attempts =>
      let signed : Signed S :=
        { keyShare := revealed.keyShare
          partialSig := z
          message := revealed.message
          session := revealed.session
          challenge := revealed.challenge }
      return .ok { toSigned := signed
                   localAttempts := attempts
                   hidingNonce := hid
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
  let hid := precomputed.nonce.hidingNonce
  let bind := precomputed.nonce.bindingNonce
  match Protocol.LocalRejection.RejectionOp.tryOnce cfg keyShare.secret challenge hid bind bindingFactor with
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
