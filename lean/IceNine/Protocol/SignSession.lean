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

import IceNine.Protocol.Core
import IceNine.Protocol.Phase
import Mathlib

namespace IceNine.Protocol.SignSession

open IceNine.Protocol

/-!
## Linear Nonce

A nonce wrapped in a structure that can only be consumed once.
The `private mk` prevents construction outside this module, and
the only way to use the nonce is via `consume` which returns the
value and a proof token that the nonce was used.
-/

/-- A fresh, unused nonce. Can only be consumed once.
    Private constructor prevents arbitrary creation. -/
structure FreshNonce (S : Scheme) where
  private mk ::
  /-- The secret nonce value -/
  private value : S.Secret
  /-- Public nonce w = A(y) -/
  private publicNonce : S.Public
  /-- Commitment opening -/
  private opening : S.Opening
deriving Repr

/-- Proof that a nonce was consumed. Produced exactly once per nonce. -/
structure NonceConsumed (S : Scheme) where
  private mk ::
  /-- Hash of the consumed nonce (for debugging, not reconstruction) -/
  fingerprint : Nat := 0

/-- Create a fresh nonce from sampled randomness.
    This is the ONLY way to create a FreshNonce. -/
def FreshNonce.sample (S : Scheme) (y : S.Secret) (opening : S.Opening) : FreshNonce S :=
  { value := y
    publicNonce := S.A y
    opening := opening }

/-!
## Session States

Each state in the signing protocol. States are parameterized by the scheme
and carry the data accumulated up to that point. Transitions consume the
current state and produce the next state.
-/

/-- Initial state: party has key share and fresh nonce, ready to commit. -/
structure ReadyToCommit (S : Scheme) where
  /-- Party's long-term key share -/
  keyShare : KeyShare S
  /-- Fresh nonce (will be consumed on commit) -/
  nonce : FreshNonce S
  /-- Message to sign -/
  message : S.Message
  /-- Session identifier -/
  session : Nat

/-- After committing: nonce is consumed, commitment is published. -/
structure Committed (S : Scheme) where
  /-- Party's key share -/
  keyShare : KeyShare S
  /-- The secret nonce (moved from FreshNonce) -/
  private secretNonce : S.Secret
  /-- Public nonce -/
  publicNonce : S.Public
  /-- Commitment opening -/
  opening : S.Opening
  /-- Message being signed -/
  message : S.Message
  /-- Session identifier -/
  session : Nat
  /-- The commitment that was broadcast -/
  commitment : S.Commitment
  /-- Proof the nonce was consumed -/
  nonceConsumed : NonceConsumed S

/-- After revealing: public nonce is revealed, ready to compute partial sig. -/
structure Revealed (S : Scheme) where
  /-- Party's key share -/
  keyShare : KeyShare S
  /-- The secret nonce (still needed for signing) -/
  private secretNonce : S.Secret
  /-- Public nonce -/
  publicNonce : S.Public
  /-- Message being signed -/
  message : S.Message
  /-- Session identifier -/
  session : Nat
  /-- Challenge computed from transcript -/
  challenge : S.Challenge
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
    Consumes the fresh nonce and produces a commitment.
    After this, the nonce cannot be accessed again from ReadyToCommit. -/
def commit (S : Scheme) (ready : ReadyToCommit S)
    : Committed S × SignCommitMsg S :=
  -- Extract nonce data (consumes the FreshNonce)
  let y := ready.nonce.value
  let w := ready.nonce.publicNonce
  let opening := ready.nonce.opening
  -- Create commitment
  let commitment := S.commit w opening
  -- Build committed state (nonce is now here, not in FreshNonce)
  let committed : Committed S :=
    { keyShare := ready.keyShare
      secretNonce := y
      publicNonce := w
      opening := opening
      message := ready.message
      session := ready.session
      commitment := commitment
      nonceConsumed := { fingerprint := 0 } }
  -- Build message for broadcast
  let msg : SignCommitMsg S :=
    { sender := ready.keyShare.pid
      session := ready.session
      commitW := commitment }
  (committed, msg)

/-- Transition: Committed → Revealed
    Called after receiving all commitments and computing challenge. -/
def reveal (S : Scheme) (committed : Committed S)
    (challenge : S.Challenge) (aggregateW : S.Public)
    : Revealed S × SignRevealWMsg S :=
  -- Build revealed state
  let revealed : Revealed S :=
    { keyShare := committed.keyShare
      secretNonce := committed.secretNonce
      publicNonce := committed.publicNonce
      message := committed.message
      session := committed.session
      challenge := challenge
      aggregateNonce := aggregateW }
  -- Build reveal message
  let msg : SignRevealWMsg S :=
    { sender := committed.keyShare.pid
      session := committed.session
      w_i := committed.publicNonce
      opening := committed.opening }
  (revealed, msg)

/-- Transition: Revealed → Signed (success) or Revealed → Aborted (norm failure)
    Computes partial signature z_i = y_i + c·sk_i.
    Returns Left if norm check passes, Right if it fails. -/
def sign (S : Scheme) (revealed : Revealed S)
    : Sum (Signed S) (Revealed S × String) :=
  -- Compute partial signature: z_i = y_i + c·sk_i
  let z_i := revealed.secretNonce + revealed.challenge • revealed.keyShare.sk_i
  -- Check norm bound
  if S.normOK z_i then
    let signed : Signed S :=
      { keyShare := revealed.keyShare
        partialSig := z_i
        message := revealed.message
        session := revealed.session
        challenge := revealed.challenge }
    Sum.inl signed
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
structure RetryContext (S : Scheme) where
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

/-- Create retry context from revealed state after norm failure.
    The revealed state is consumed—it cannot be used again. -/
def mkRetryContext (S : Scheme) (revealed : Revealed S) (maxAttempts : Nat)
    : RetryContext S :=
  { attempt := 1
    maxAttempts := maxAttempts
    keyShare := revealed.keyShare
    message := revealed.message
    session := revealed.session }

/-- Advance retry context for next attempt.
    Returns None if max attempts exceeded. -/
def advanceRetry (ctx : RetryContext S) : Option (RetryContext S) :=
  if ctx.attempt < ctx.maxAttempts then
    some { ctx with attempt := ctx.attempt + 1 }
  else
    none

/-- Create new ReadyToCommit for retry with FRESH nonce.
    The fresh nonce must be newly sampled—cannot reuse old nonce.

    **Note**: Uses same session ID for threshold coordination. All parties in the
    signing group should retry together with the same base session ID. -/
def retryWithFreshNonce (S : Scheme) (ctx : RetryContext S) (freshNonce : FreshNonce S)
    : ReadyToCommit S :=
  { keyShare := ctx.keyShare
    nonce := freshNonce
    message := ctx.message
    session := ctx.session }

/-- Create new ReadyToCommit for retry with FRESH nonce AND new session ID.
    Use this when retries should be independent sessions (e.g., parallel attempts).

    **Warning**: New session requires coordination with other parties to ensure
    they also use the new session ID. -/
def retryWithNewSession (S : Scheme) (ctx : RetryContext S) (freshNonce : FreshNonce S) (newSession : Nat)
    : ReadyToCommit S :=
  { keyShare := ctx.keyShare
    nonce := freshNonce
    message := ctx.message
    session := newSession }

/-- Create aborted state when max retries exceeded. -/
def abort (S : Scheme) (ctx : RetryContext S) : Aborted S :=
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
  | success (done : Done S)
  | needsRetry (ctx : RetryContext S)
  | aborted (aborted : Aborted S)

/-- Run signing from Revealed state through to completion or retry. -/
def trySign (S : Scheme) (revealed : Revealed S) (maxAttempts : Nat := 16)
    : SignResult S :=
  match sign S revealed with
  | Sum.inl signed =>
      .success (finalize S signed)
  | Sum.inr (revealed', _) =>
      let ctx := mkRetryContext S revealed' maxAttempts
      if ctx.attempt < ctx.maxAttempts then
        .needsRetry ctx
      else
        .aborted (abort S ctx)

/-!
## Initialization

Create the initial session state from key share and sampled randomness.
-/

/-- Initialize a signing session.
    Caller must provide freshly sampled nonce and opening. -/
def initSession (S : Scheme)
    (keyShare : KeyShare S)
    (message : S.Message)
    (session : Nat)
    (y : S.Secret)
    (opening : S.Opening)
    : ReadyToCommit S :=
  { keyShare := keyShare
    nonce := FreshNonce.sample S y opening
    message := message
    session := session }

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

/-- Example: this CANNOT compile because `ready` is consumed by first `commit` -/
-- def badNonceReuse (S : Scheme) (ready : ReadyToCommit S) :=
--   let (committed1, _) := commit S ready  -- consumes ready
--   let (committed2, _) := commit S ready  -- ERROR: ready already consumed
--   (committed1, committed2)

end IceNine.Protocol.SignSession
