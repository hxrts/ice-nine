/-
# Nonce Lifecycle Effect Abstraction

Unified effect abstraction for nonce management in threshold signing.
Consolidates session tracking, nonce registry, and pool management into
a single composable effect signature with explicit error handling.

## Design Philosophy

Following the effect signature + handler pattern (similar to ByteRead/ByteReader
in Serialize.lean), we separate:

1. **NonceState**: Pure effect state containing all nonce-related data
2. **NonceOp**: Pure operations on the state returning `NonceResult`
3. **NonceM**: Monadic wrapper for composing operations

This separation allows:
- Testing pure operations directly
- Composing operations monadically when convenient
- Clear error handling at each step

## Nonce Safety Invariants

1. **Session uniqueness**: Each session ID used at most once per party
2. **Commitment uniqueness**: Each nonce commitment used at most once
3. **Consumption tracking**: Nonces are consumed exactly once
4. **Expiry enforcement**: Precomputed nonces expire and cannot be used

The type system + runtime checks enforce these invariants.
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.Core.Error
import IceNine.Protocol.Sign.Types
import IceNine.Protocol.Sign.Session
import Mathlib

namespace IceNine.Protocol.NonceLifecycle

open IceNine.Protocol
open IceNine.Protocol.Error
open IceNine.Protocol.SignSession

/-!
## Integration with Session Types

This module provides runtime nonce tracking that **complements** the compile-time
guarantees from `Sign/Session.lean`. The session types ensure:

1. `FreshNonce` can only be created via `FreshNonce.sample`
2. `FreshNonce` is consumed exactly once by `commit`
3. State transitions are linear: Ready → Committed → Revealed → Signed → Done

This module adds **runtime detection** for:
- Session ID reuse across different signing attempts
- Commitment reuse (same nonce used in multiple sessions)
- Pool management for precomputed nonces

**Design**: `NonceState` can replace the separate `SessionTracker` and `NonceRegistry`
that are threaded through session transitions, providing a unified interface with
better error reporting via `BlameableError`.
-/

/-!
## Nonce Lifecycle Errors

Typed errors for nonce operations, enabling precise error handling.
Integrates with the BlameableError infrastructure from Core/Error.lean.
-/

/-- Errors that can occur during nonce lifecycle operations.

    **Blame attribution**: Some errors identify a potentially misbehaving party:
    - `commitmentReuse`: indicates the party may be attempting nonce reuse attack
    - Others are operational errors without blame -/
inductive NonceError (PartyId : Type*)
  | sessionAlreadyUsed (session : Nat) (party : Option PartyId)
      -- Attempt to use a session ID that was already used
  | commitmentReuse (session1 session2 : Nat) (party : PartyId)
      -- Same nonce commitment appeared in two different sessions (SECURITY!)
  | nonceExpired (generatedAt currentTime maxAge : Nat)
      -- Precomputed nonce has expired
  | poolEmpty
      -- No available nonces in pool
  | poolExhausted (consumed : Nat)
      -- Pool has been exhausted (for diagnostics)
  | invalidSession (reason : String)
      -- Session validation failed
  | nonceNotFound (session : Nat)
      -- Requested nonce not found in registry
  deriving Repr

/-- NonceError implements BlameableError.
    Commitment reuse is a security violation that identifies the faulty party. -/
instance {PartyId : Type*} : BlameableError (NonceError PartyId) PartyId where
  blamedParty
    | .sessionAlreadyUsed _ p => p
    | .commitmentReuse _ _ p => some p  -- Security violation!
    | .nonceExpired _ _ _ => none
    | .poolEmpty => none
    | .poolExhausted _ => none
    | .invalidSession _ => none
    | .nonceNotFound _ => none

/-- Convert NonceError to descriptive string. -/
def NonceError.toString {PartyId : Type*} [ToString PartyId] : NonceError PartyId → String
  | .sessionAlreadyUsed session party =>
      match party with
      | some p => s!"session {session} already used by party {p}"
      | none => s!"session {session} has already been used"
  | .commitmentReuse s1 s2 p =>
      s!"SECURITY: nonce commitment from {p} reused in sessions {s1} and {s2}"
  | .nonceExpired gen cur max =>
      s!"nonce expired: generated at {gen}, current time {cur}, max age {max}"
  | .poolEmpty =>
      "nonce pool is empty"
  | .poolExhausted consumed =>
      s!"nonce pool exhausted after {consumed} nonces"
  | .invalidSession reason =>
      s!"invalid session: {reason}"
  | .nonceNotFound session =>
      s!"nonce for session {session} not found"

instance {PartyId : Type*} [ToString PartyId] : ToString (NonceError PartyId) :=
  ⟨NonceError.toString⟩

/-!
## Nonce State

The consolidated state for all nonce-related tracking.
Combines SessionTracker, NonceRegistry, and NoncePool into one structure.
-/

/-- Consolidated nonce lifecycle state.

    Tracks:
    - Used sessions (per-party)
    - Committed nonces (for reuse detection)
    - Precomputed nonce pool (for fast path)

    **Invariants**:
    - `usedSessions` contains all sessions where commit has occurred
    - `byCommitment` maps commitments to session lists for reuse detection
    - `pool` contains only unconsumed precomputed nonces -/
structure NonceState (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment] where
  /-- Party ID this state belongs to -/
  partyId : S.PartyId
  /-- Set of used session IDs -/
  usedSessions : Finset Nat
  /-- Primary index: (partyId, session) → commitment -/
  commitBySession : Std.HashMap (S.PartyId × Nat) S.Commitment
  /-- Reverse index: (partyId, commitment) → list of sessions -/
  sessionsByCommit : Std.HashMap (S.PartyId × S.Commitment) (List Nat)
  /-- Pool of precomputed nonces -/
  poolAvailable : List (PrecomputedNonce S)
  /-- Count of consumed nonces (statistics) -/
  poolConsumed : Nat

/-- Create empty nonce state for a party. -/
def NonceState.empty (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (pid : S.PartyId) : NonceState S :=
  { partyId := pid
    usedSessions := ∅
    commitBySession := {}
    sessionsByCommit := {}
    poolAvailable := []
    poolConsumed := 0 }

/-!
## Pure Operations (Effect Signature)

Each operation takes state and returns `NonceResult`, a pair of
result value and updated state, wrapped in `Except` for errors.
-/

/-- Result of a nonce operation: value and updated state. -/
abbrev NonceResult (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (α : Type) := Except (NonceError S.PartyId) (α × NonceState S)

namespace NonceOp

variable {S : Scheme}
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    {α : Type}
    {α : Type}

/-- Check if a session ID is fresh (not previously used). -/
def isFresh (session : Nat) (st : NonceState S) : Bool × NonceState S :=
  (session ∉ st.usedSessions, st)

/-- Check session freshness, returning error if already used. -/
def checkFresh (session : Nat) (st : NonceState S) : NonceResult S Unit :=
  if session ∈ st.usedSessions then
    .error (.sessionAlreadyUsed session (some st.partyId))
  else
    .ok ((), st)

/-- Mark a session as used. -/
def markUsed (session : Nat) (st : NonceState S) : NonceResult S Unit :=
  .ok ((), { st with usedSessions := Insert.insert session st.usedSessions })

/-- Record a nonce commitment for a session. -/
def recordCommitment (session : Nat) (commit : S.Commitment)
    (st : NonceState S) : NonceResult S Unit :=
  let pid := st.partyId
  let newBySession := st.commitBySession.insert (pid, session) commit
  let key := (pid, commit)
  let sessions := st.sessionsByCommit.get? key |>.getD []
  let newByCommit := st.sessionsByCommit.insert key (session :: sessions)
  .ok ((), { st with
    commitBySession := newBySession
    sessionsByCommit := newByCommit })

/-- Check for nonce reuse (same commitment in different sessions). -/
def detectReuse (commit : S.Commitment) (st : NonceState S)
    : NonceResult S (Option (Nat × Nat)) :=
  let pid := st.partyId
  match st.sessionsByCommit.get? (pid, commit) with
  | some (s1 :: s2 :: _) =>
      if s1 ≠ s2 then .ok (some (s1, s2), st)
      else .ok (none, st)
  | _ => .ok (none, st)

/-- Check for reuse and throw error if detected.
    This is a **security-critical** check - reuse enables key recovery! -/
def assertNoReuse (commit : S.Commitment) (st : NonceState S)
    : NonceResult S Unit :=
  match detectReuse commit st with
  | .ok (reuse, st') =>
      match reuse with
      | some (s1, s2) => .error (.commitmentReuse s1 s2 st.partyId)
      | none => .ok ((), st')
  | .error e => .error e

/-- Add a precomputed nonce to the pool. -/
def addToPool (pn : PrecomputedNonce S) (st : NonceState S)
    : NonceResult S Unit :=
  .ok ((), { st with poolAvailable := pn :: st.poolAvailable })

/-- Take a valid nonce from the pool, pruning expired ones.
    Returns the nonce and updated state, or error if pool empty. -/
def takeFromPool (currentTime : Nat) (st : NonceState S)
    : NonceResult S (PrecomputedNonce S) :=
  -- Filter out expired nonces
  let valid := st.poolAvailable.filter (fun pn => pn.isValid currentTime)
  match valid with
  | [] =>
      if st.poolConsumed > 0 then
        .error (.poolExhausted st.poolConsumed)
      else
        .error .poolEmpty
  | pn :: rest =>
      .ok (pn, { st with
        poolAvailable := rest
        poolConsumed := st.poolConsumed + 1 })

/-- Get pool statistics. -/
def poolStats (currentTime : Nat) (st : NonceState S)
    : (Nat × Nat × Nat) × NonceState S :=
  let total := st.poolAvailable.length
  let valid := (st.poolAvailable.filter (fun pn => pn.isValid currentTime)).length
  ((total, valid, st.poolConsumed), st)

/-- Prune expired nonces from pool. -/
def prunePool (currentTime : Nat) (st : NonceState S)
    : NonceResult S Nat :=
  let before := st.poolAvailable.length
  let valid := st.poolAvailable.filter (fun pn => pn.isValid currentTime)
  let pruned := before - valid.length
  .ok (pruned, { st with poolAvailable := valid })

/-- Full commit operation: check fresh, mark used, record, check reuse.
    This is the primary operation for starting a signing session. -/
def commitSession (session : Nat) (commit : S.Commitment)
    (st : NonceState S) : NonceResult S Unit :=
  match checkFresh session st with
  | .error e => .error e
  | .ok ((), st) =>
      match markUsed session st with
      | .error e => .error e
      | .ok ((), st) =>
          match recordCommitment session commit st with
          | .error e => .error e
          | .ok ((), st) => assertNoReuse commit st

end NonceOp

/-!
## Monadic Wrapper (Handler)

`NonceM` provides monadic composition for chaining operations.
-/

/-- Nonce monad: StateT wrapper for composing nonce operations. -/
abbrev NonceM (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment] :=
  StateT (NonceState S) (Except (NonceError S.PartyId))

namespace NonceM

variable {S : Scheme}
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]

/-- Lift a pure operation into NonceM. -/
def lift {α : Type} (op : NonceState S → NonceResult S α) : NonceM S α := do
  let st ← get
  match op st with
  | .ok (a, st') => set st'; pure a
  | .error e => throw e

/-- Run NonceM, returning final state and result or error. -/
def run {α : Type} (m : NonceM S α) (st : NonceState S)
    : Except (NonceError S.PartyId) (α × NonceState S) :=
  StateT.run m st

/-- Run NonceM, discarding final state. -/
def eval {α : Type} (m : NonceM S α) (st : NonceState S)
    : Except (NonceError S.PartyId) α :=
  match StateT.run m st with
  | .ok (a, _) => .ok a
  | .error e => .error e

/-- Run NonceM, returning only final state. -/
def exec {α : Type} (m : NonceM S α) (st : NonceState S)
    : Except (NonceError S.PartyId) (NonceState S) :=
  match StateT.run m st with
  | .ok (_, st') => .ok st'
  | .error e => .error e

-- Lifted operations

/-- Check if session is fresh. -/
def isFresh (session : Nat) : NonceM S Bool := do
  let st ← get
  pure (session ∉ st.usedSessions)

/-- Check session freshness, throwing if already used. -/
def checkFresh (session : Nat) : NonceM S Unit :=
  lift (NonceOp.checkFresh session)

/-- Mark session as used. -/
def markUsed (session : Nat) : NonceM S Unit :=
  lift (NonceOp.markUsed session)

/-- Record a commitment. -/
def recordCommitment (session : Nat) (commit : S.Commitment) : NonceM S Unit :=
  lift (NonceOp.recordCommitment session commit)

/-- Detect nonce reuse. -/
def detectReuse (commit : S.Commitment) : NonceM S (Option (Nat × Nat)) :=
  lift (NonceOp.detectReuse commit)

/-- Assert no reuse, throwing if detected. -/
def assertNoReuse (commit : S.Commitment) : NonceM S Unit :=
  lift (NonceOp.assertNoReuse commit)

/-- Add nonce to pool. -/
def addToPool (pn : PrecomputedNonce S) : NonceM S Unit :=
  lift (NonceOp.addToPool pn)

/-- Take nonce from pool. -/
def takeFromPool (currentTime : Nat) : NonceM S (PrecomputedNonce S) :=
  lift (NonceOp.takeFromPool currentTime)

/-- Prune expired nonces. -/
def prunePool (currentTime : Nat) : NonceM S Nat :=
  lift (NonceOp.prunePool currentTime)

/-- Full commit operation. -/
def commitSession (session : Nat) (commit : S.Commitment) : NonceM S Unit :=
  lift (NonceOp.commitSession session commit)

end NonceM

/-!
## Compatibility Layer

Functions to convert between the new unified state and legacy types.
-/

/-- Create NonceState from legacy SessionTracker and NonceRegistry. -/
def NonceState.fromLegacy (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (tracker : SessionTracker S) (registry : NonceRegistry S)
    : NonceState S :=
  { partyId := tracker.partyId
    usedSessions := tracker.usedSessions
    commitBySession := registry.bySession
    sessionsByCommit := registry.byCommitment
    poolAvailable := []
    poolConsumed := 0 }

/-- Extract legacy SessionTracker from NonceState. -/
def NonceState.toSessionTracker {S : Scheme}
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (st : NonceState S) : SessionTracker S :=
  { usedSessions := st.usedSessions
    partyId := st.partyId }

/-- Extract legacy NonceRegistry from NonceState. -/
def NonceState.toNonceRegistry {S : Scheme}
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (st : NonceState S) : NonceRegistry S :=
  { bySession := st.commitBySession
    byCommitment := st.sessionsByCommit }

/-- Extract legacy NoncePool from NonceState. -/
def NonceState.toNoncePool {S : Scheme}
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (st : NonceState S) : NoncePool S :=
  { available := st.poolAvailable
    consumedCount := st.poolConsumed }

/-!
## Conversion Utilities

Integrate with Error.lean utilities.
-/

/-- Convert NonceResult to Option, discarding error info.
    Uses Error.exceptToOption from Core/Error.lean. -/
def NonceResult.toOption {S : Scheme}
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    {α : Type} (r : NonceResult S α) : Option (α × NonceState S) :=
  exceptToOption r

/-- Check if result is an error. -/
def NonceResult.isError {S : Scheme}
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    {α : Type} (r : NonceResult S α) : Bool :=
  match r with
  | .error _ => true
  | .ok _ => false

/-- Get error from result if present. -/
def NonceResult.getError? {S : Scheme}
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    {α : Type} (r : NonceResult S α) : Option (NonceError S.PartyId) :=
  match r with
  | .error e => some e
  | .ok _ => none

/-!
## Session-Type Integration

These functions bridge `NonceLifecycle` with the linear session types from
`Sign/Session.lean`, enabling use of `NonceState` in place of separate
`SessionTracker` and `NonceRegistry` threading.
-/

/-- Create a ReadyToCommit state using NonceState for tracking.

    This bridges the session type system with NonceLifecycle:
    - Takes a `FreshNonce` (linear, will be consumed by `commit`)
    - Uses `NonceState` instead of separate tracker/registry

    **Usage**: Replace `initSession` when using NonceLifecycle for tracking. -/
def initSessionWithState (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (keyShare : KeyShare S)
    (message : S.Message)
    (session : Nat)
    (nonce : FreshNonce S)
    (st : NonceState S)
    : ReadyToCommit S :=
  { keyShare := keyShare
    nonce := nonce
    message := message
    session := session
    tracker := st.toSessionTracker
    nonceReg := st.toNonceRegistry }

/-- Commit transition that updates NonceState.

    Wraps `SignSession.commit` but:
    - Takes `NonceState` instead of separate tracker/registry
    - Returns updated `NonceState` with the commit recorded
    - Uses `NonceError` for better error reporting

    **Linear guarantee**: The `FreshNonce` inside `ready` is consumed by this call.
    The session type system ensures it cannot be reused. -/
def commitWithState (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (ready : ReadyToCommit S)
    (st : NonceState S)
    : Except (NonceError S.PartyId) (Committed S × SignCommitMsg S × NonceState S) := do
  -- First check using our typed errors
  let ((), st) ← NonceOp.checkFresh ready.session st
  -- Perform the commit (consumes FreshNonce)
  match SignSession.commit S ready with
  | .error e =>
      match e with
      | .sessionMismatch s1 s2 =>
          if s1 = s2 then
            .error (.sessionAlreadyUsed s1 (some st.partyId))
          else
            .error (.commitmentReuse s1 s2 st.partyId)
      | _ => .error (.invalidSession "commit failed")
  | .ok result =>
      -- Record in our state
      let ((), st) ← NonceOp.markUsed ready.session st
      let ((), st) ← NonceOp.recordCommitment ready.session result.msg.commitW st
      -- Check for reuse with our error type
      let ((), st) ← NonceOp.assertNoReuse result.msg.commitW st
      .ok (result.committed, result.msg, st)

/-- Take a precomputed nonce from pool and create ReadyToCommit.

    **Linear guarantee**: Returns a `FreshNonce` wrapped in `ReadyToCommit`.
    The caller must call `commitWithState` to consume it - the session type
    system prevents any other use.

    **Runtime check**: Validates nonce hasn't expired before returning. -/
def takeAndPrepare (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (keyShare : KeyShare S)
    (message : S.Message)
    (session : Nat)
    (currentTime : Nat)
    (st : NonceState S)
    : Except (NonceError S.PartyId) (ReadyToCommit S × NonceState S) := do
  -- Take from pool (validates expiry)
  let (pn, st) ← NonceOp.takeFromPool currentTime st
  -- The PrecomputedNonce contains a FreshNonce
  let ready := initSessionWithState S keyShare message session pn.nonce st
  .ok (ready, st)

/-- Full signing session setup with NonceState.

    Combines pool management with session initialization:
    1. Takes valid nonce from pool
    2. Creates ReadyToCommit state
    3. Returns state ready for `commitWithState`

    **Type flow**:
    ```
    NonceState ──takeAndPrepare──► ReadyToCommit (contains FreshNonce)
                                        │
                                        ▼ commitWithState
                                   Committed (FreshNonce consumed)
    ```
-/
def prepareSigningSession (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId]
    [BEq S.Commitment] [Hashable S.Commitment]
    (keyShare : KeyShare S)
    (message : S.Message)
    (session : Nat)
    (currentTime : Nat)
    (st : NonceState S)
    : Except (NonceError S.PartyId) (ReadyToCommit S × NonceState S) :=
  takeAndPrepare S keyShare message session currentTime st

/-!
## Usage Example

```lean
-- With session type integration
let st0 := NonceState.empty S pid

-- Add precomputed nonces to pool
let st1 ← NonceM.exec (NonceM.addToPool pn1) st0
let st2 ← NonceM.exec (NonceM.addToPool pn2) st1

-- Prepare signing session (takes FreshNonce from pool)
let (ready, st3) ← prepareSigningSession S keyShare msg session currentTime st2

-- Commit (consumes the FreshNonce - enforced by session types)
let (committed, commitMsg, st4) ← commitWithState S ready st3

-- The FreshNonce is now consumed - cannot be reused
-- Session types make this a compile-time guarantee
-- NonceState provides runtime detection as defense-in-depth

-- Pure operation style (without session types)
let ((), st1) ← NonceOp.checkFresh 42 st0
let ((), st2) ← NonceOp.markUsed 42 st1
let ((), st3) ← NonceOp.recordCommitment 42 commit st2

-- Error handling with blame
match result with
| .ok (_, st') => -- success
| .error e =>
    match BlameableError.blamedParty e with
    | some party => -- security violation by party
    | none => -- operational error
```
-/

end IceNine.Protocol.NonceLifecycle
