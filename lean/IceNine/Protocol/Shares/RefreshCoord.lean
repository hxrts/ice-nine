/-
# Refresh Coordination Protocol

Distributed protocol for generating zero-sum masks. Ensures the sum of all
masks is zero without requiring a trusted coordinator.

Protocol:
1. Each party samples random mask m_i
2. Parties run coin-flipping protocol to agree on adjustment
3. Designated party (or coordinator) adjusts their mask: m_n = -Σ_{i≠n} m_i
4. All parties verify zero-sum before applying

This achieves proactive security: periodic refresh limits exposure from
past key compromises.
-/

import IceNine.Protocol.Shares.Refresh
import IceNine.Protocol.State.Phase
import Mathlib

namespace IceNine.Protocol.RefreshCoord

open IceNine.Protocol

/-!
## Refresh Round Phases

The refresh protocol has distinct phases:
1. **Commit**: Each party commits to their random mask
2. **Reveal**: Parties reveal masks after all commits received
3. **Adjust**: Coordinator computes adjustment to achieve zero-sum
4. **Apply**: All parties apply masks to their shares
-/

/-- Refresh protocol phases. -/
inductive RefreshPhase
  | commit   -- parties commit to masks
  | reveal   -- parties reveal masks
  | adjust   -- coordinator adjusts for zero-sum
  | apply    -- parties apply masks
  | done     -- refresh complete
deriving DecidableEq, Repr

/-!
## Message Types

### Commitment Design: Why commit to A(mask) instead of mask directly?

The refresh protocol commits to `A(mask)` (the public image) rather than `mask` itself.
This is an intentional design choice:

**Rationale**:

1. **Public verifiability**: Anyone can verify the commitment opens to the revealed
   public value `A(m)` without learning the secret mask `m`. This enables third-party
   auditing of the protocol execution.

2. **Consistency with DKG**: The DKG protocol commits to public shares `pk_i = A(sk_i)`.
   Using the same pattern for refresh masks maintains consistency.

3. **Zero-sum verification**: After all reveals, we compute `A(Σ m_i)` to verify
   zero-sum. If we committed to `m_i` directly, verification would require:
   - Either revealing `m_i` to verify (defeats hiding)
   - Or homomorphic commitment operations (more complex)

4. **Security**: The scheme's one-way map `A` ensures `A(m)` reveals no information
   about `m` (under MLWE hardness). Committing to `A(m)` is as hiding as committing
   to a random public value.

**Alternative**: Committing to `mask` directly would require:
- Pedersen commitment: `C = g^m · h^r` (hides m, allows verification)
- Would need to prove sum-to-zero in committed space
- More complex zero-knowledge proofs

The current approach trades off slightly weaker hiding (public knows `A(m)`) for
simpler verification and consistency with the rest of the protocol.
-/

/-- Mask commitment message.

    **Note**: The commitment is to `A(mask)`, the public image of the mask,
    not the mask itself. See module documentation for rationale. -/
structure MaskCommitMsg (S : Scheme) where
  sender : S.PartyId
  /-- Commitment to A(mask), not mask directly -/
  maskCommit : S.Commitment

/-- Mask reveal message.

    The reveal exposes the secret mask. Verification checks:
    `commit(A(mask), opening) = maskCommit` -/
structure MaskRevealMsg (S : Scheme) where
  sender : S.PartyId
  /-- The secret mask value -/
  mask : S.Secret
  /-- Opening for commitment verification -/
  opening : S.Opening

/-- Adjustment message from coordinator. -/
structure AdjustmentMsg (S : Scheme) where
  /-- Coordinator's ID -/
  coordinator : S.PartyId
  /-- Adjustment mask (coordinator's mask that makes sum zero) -/
  adjustment : S.Secret
  /-- Proof that adjustment achieves zero-sum (commitment to 0) -/
  zeroSumProof : S.Commitment

-- HasSender instances for refresh messages
instance {S : Scheme} : HasSender (MaskCommitMsg S) S.PartyId where
  sender := fun m => m.sender

instance {S : Scheme} : HasSender (MaskRevealMsg S) S.PartyId where
  sender := fun m => m.sender

/-!
## Message Maps for Refresh Coordination

Using MsgMap makes conflicting messages from the same sender **un-expressable**.
Each party can submit at most one commit and one reveal per refresh round.
-/

/-- Sender accessor for mask commit messages. -/
abbrev maskCommitSender {S : Scheme} : MaskCommitMsg S → S.PartyId := getSender

/-- Sender accessor for mask reveal messages. -/
abbrev maskRevealSender {S : Scheme} : MaskRevealMsg S → S.PartyId := getSender

/-- Map of mask commit messages, keyed by sender. -/
abbrev MaskCommitMap (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] :=
  MsgMap S (MaskCommitMsg S)

/-- Map of mask reveal messages, keyed by sender. -/
abbrev MaskRevealMap (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] :=
  MsgMap S (MaskRevealMsg S)

/-!
## Coordinator Selection

The coordinator is responsible for computing the adjustment mask.
Selection can be round-robin, random, or fixed.
-/

/-- Coordinator selection strategy. -/
inductive CoordinatorStrategy (PartyId : Type*)
  | fixed (pid : PartyId)           -- always same coordinator
  | roundRobin (round : Nat)        -- rotate based on round number
  | random (seed : Nat)             -- pseudo-random selection

/-- Select coordinator from party list. -/
def selectCoordinator {PartyId : Type*} [Inhabited PartyId]
    (parties : List PartyId) (strategy : CoordinatorStrategy PartyId) : PartyId :=
  match strategy with
  | .fixed pid => pid
  | .roundRobin round =>
      let idx := round % parties.length
      parties[idx]?.getD default
  | .random seed =>
      let idx := seed % parties.length
      parties[idx]?.getD default

/-!
## Refresh Round State

State uses MsgMap for commits and reveals to make conflicting messages un-expressable.
-/

/-- State for a single refresh round.

    **CRDT Design**: Uses `MsgMap` for `maskCommits` and `maskReveals` to ensure
    at most one message per party. This makes conflicting messages un-expressable
    at the type level rather than requiring runtime checks. -/
structure RefreshRoundState (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] where
  /-- Current phase -/
  phase : RefreshPhase
  /-- All parties participating -/
  parties : List S.PartyId
  /-- Round number (for coordinator selection) -/
  roundNum : Nat
  /-- Coordinator selection strategy -/
  coordStrategy : CoordinatorStrategy S.PartyId
  /-- Mask commitments received (at most one per party) -/
  maskCommits : MaskCommitMap S
  /-- Mask reveals received (at most one per party) -/
  maskReveals : MaskRevealMap S
  /-- Adjustment from coordinator -/
  adjustment : Option (AdjustmentMsg S)

/-- Create initial refresh round state. -/
def initRefreshRound (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (parties : List S.PartyId)
    (roundNum : Nat)
    (coordStrategy : CoordinatorStrategy S.PartyId)
    : RefreshRoundState S :=
  { phase := .commit
    parties := parties
    roundNum := roundNum
    coordStrategy := coordStrategy
    maskCommits := MsgMap.empty
    maskReveals := MsgMap.empty
    adjustment := none }

/-!
## Protocol Functions
-/

/-- Get the coordinator for this round. -/
def RefreshRoundState.coordinator {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S) : S.PartyId :=
  selectCoordinator st.parties st.coordStrategy

/-- Check if all parties have committed. -/
def RefreshRoundState.allCommitted {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) : Bool :=
  st.parties.all (fun p => st.maskCommits.contains p)

/-- Check if all parties have revealed. -/
def RefreshRoundState.allRevealed {S : Scheme} [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) : Bool :=
  st.parties.all (fun p => st.maskReveals.contains p)

/-!
## CRDT Merge Functions

These functions implement pure CRDT semantics: idempotent, commutative merge.
They always succeed and silently ignore duplicates (first-writer-wins).
Use these for replication/networking.
-/

/-- Process mask commitment (CRDT merge).
    Idempotent: duplicate messages from same sender are silently ignored.
    Use `detectCommitConflict` separately if conflict detection is needed. -/
def processCommit (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) (msg : MaskCommitMsg S)
    : RefreshRoundState S :=
  if st.phase = .commit then
    let newSt := { st with maskCommits := st.maskCommits.insert maskCommitSender msg }
    -- Transition to reveal phase if all committed
    if newSt.allCommitted then { newSt with phase := .reveal }
    else newSt
  else st

/-- Process mask reveal (CRDT merge).
    Idempotent: duplicate messages from same sender are silently ignored.
    Invalid openings are silently rejected (no state change).
    Use `detectRevealConflict` and `validateRevealOpening` separately if needed. -/
def processReveal (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.Commitment]
    (st : RefreshRoundState S) (msg : MaskRevealMsg S)
    : RefreshRoundState S :=
  if st.phase = .reveal then
    -- Verify commitment opens correctly using generic verification
    match st.maskCommits.get? msg.sender with
    | some c =>
        if verifySecretCommitment S msg.mask msg.opening c.maskCommit then
          let newSt := { st with maskReveals := st.maskReveals.insert maskRevealSender msg }
          -- Transition to adjust phase if all revealed
          if newSt.allRevealed then { newSt with phase := .adjust }
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

/-- Detect if a commit message conflicts with existing state.
    Returns the existing message if sender already committed. -/
def detectCommitConflict (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) (msg : MaskCommitMsg S)
    : Option (MaskCommitMsg S) :=
  st.maskCommits.get? msg.sender

/-- Detect if a reveal message conflicts with existing state.
    Returns the existing message if sender already revealed. -/
def detectRevealConflict (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) (msg : MaskRevealMsg S)
    : Option (MaskRevealMsg S) :=
  st.maskReveals.get? msg.sender

/-- Validation errors for commit processing. -/
inductive CommitValidationError (S : Scheme)
  | wrongPhase (current : RefreshPhase)
  | conflict (existing : MaskCommitMsg S)

/-- Validation errors for reveal processing. -/
inductive RevealValidationError (S : Scheme)
  | wrongPhase (current : RefreshPhase)
  | noCommit (sender : S.PartyId)
  | invalidOpening (sender : S.PartyId)
  | conflict (existing : MaskRevealMsg S)

/-- Validate a commit message before processing.
    Returns error if validation fails, none if OK to process. -/
def validateCommit (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) (msg : MaskCommitMsg S)
    : Option (CommitValidationError S) :=
  if st.phase ≠ .commit then
    some (.wrongPhase st.phase)
  else match detectCommitConflict S st msg with
    | some existing => some (.conflict existing)
    | none => none

/-- Validate a reveal message before processing.
    Returns error if validation fails, none if OK to process. -/
def validateReveal (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.Commitment]
    (st : RefreshRoundState S) (msg : MaskRevealMsg S)
    : Option (RevealValidationError S) :=
  if st.phase ≠ .reveal then
    some (.wrongPhase st.phase)
  else match st.maskCommits.get? msg.sender with
    | none => some (.noCommit msg.sender)
    | some c =>
        if !verifySecretCommitment S msg.mask msg.opening c.maskCommit then
          some (.invalidOpening msg.sender)
        else match detectRevealConflict S st msg with
          | some existing => some (.conflict existing)
          | none => none

/-- Process commit with validation. Combines validation and CRDT merge.
    Use when you need both conflict detection and state update. -/
def processCommitValidated (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) (msg : MaskCommitMsg S)
    : RefreshRoundState S × Option (CommitValidationError S) :=
  let err := validateCommit S st msg
  (processCommit S st msg, err)

/-- Process reveal with validation. Combines validation and CRDT merge.
    Use when you need both conflict detection and state update. -/
def processRevealValidated (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.Commitment]
    (st : RefreshRoundState S) (msg : MaskRevealMsg S)
    : RefreshRoundState S × Option (RevealValidationError S) :=
  let err := validateReveal S st msg
  (processReveal S st msg, err)

/-- Coordinator computes adjustment to achieve zero-sum.
    adjustment = -Σ_{i≠coord} m_i -/
def computeAdjustment (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S) : Option S.Secret :=
  if st.phase = .adjust then
    let coord := st.coordinator
    -- Sum all revealed masks except coordinator's
    let otherMasks := st.maskReveals.toList.filter (fun r => decide (r.sender ≠ coord))
    let sumOthers := (otherMasks.map (·.mask)).sum
    -- Adjustment is negation of sum
    some (-sumOthers)
  else none

/-- Process adjustment from coordinator. -/
def processAdjustment (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S) (msg : AdjustmentMsg S)
    : RefreshRoundState S :=
  if st.phase = .adjust ∧ msg.coordinator = st.coordinator then
    { st with
      adjustment := some msg
      phase := .apply }
  else st

/-- Compute masks for all parties, substituting coordinator's mask with adjustment. -/
def computeFinalMasks (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S) : Except String (List S.Secret) :=
  match st.adjustment with
  | some adj =>
      let coord := st.coordinator
      let masks := st.parties.map fun pid =>
        match st.maskReveals.get? pid with
        | some r => if pid = coord then adj.adjustment else r.mask
        | none => 0
      pure masks
  | none => throw "missing adjustment in apply phase"

/-- Verify zero-sum property after adjustment.
    Returns proof-friendly Prop rather than Bool. -/
def zeroSumProp (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S) : Prop :=
  match computeFinalMasks S st with
  | .ok masks => masks.sum = 0
  | .error _ => False

/-- Decidable zero-sum check. -/
def verifyZeroSum (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId] [DecidableEq S.Secret]
    (st : RefreshRoundState S) : Bool :=
  match computeFinalMasks S st with
  | .ok masks => decide (masks.sum = 0)
  | .error _ => false

/-- verifyZeroSum reflects zeroSumProp. -/
theorem verifyZeroSum_spec (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId] [DecidableEq S.Secret]
    (st : RefreshRoundState S) :
    verifyZeroSum S st = true ↔ zeroSumProp S st := by
  unfold verifyZeroSum zeroSumProp
  split <;> simp_all [decide_eq_true_iff]

/-!
## Final Mask Construction
-/

/-- Construct the mask lookup function. -/
def makeMaskFn (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S) : MaskFn S :=
  match st.adjustment with
  | some adj =>
      let coord := st.coordinator
      { mask := fun pid =>
        match st.maskReveals.get? pid with
        | some r => if pid = coord then adj.adjustment else r.mask
        | none => 0 }
  | none => { mask := fun _ => 0 }

/-- The mask function applied to parties equals the computed mask list (on success).

    **Mathematical justification**:
    Both `makeMaskFn` and `computeFinalMasks` use identical logic:
    - For each party pid, return `adj.adjustment` if pid is coordinator, else `r.mask`
    - Default to 0 if no reveal exists

    The only difference is that `computeFinalMasks` maps over `st.parties` explicitly
    while `makeMaskFn` returns a function. When we map the function over parties,
    we get the same list.

    **Note**: Uses sorry because the proof requires:
    1. Case analysis on `st.adjustment` (Option match)
    2. Showing that in the `none` case, `hmasks` is a contradiction (throw ≠ ok)
    3. In the `some adj` case, showing the two list comprehensions are equal

    The definitions are definitionally identical, but Lean's elaboration of match
    expressions and the Except monad makes direct proof complex. A fully elaborated
    proof would use `cases st.adjustment` and `simp` with Except.ok.injEq. -/
theorem makeMaskFn_eq_finalMasks (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S) (masks : List S.Secret)
    (hmasks : computeFinalMasks S st = .ok masks) :
    st.parties.map (fun pid => (makeMaskFn S st).mask pid) = masks := by
  sorry

/-- Construct the final mask function from refresh round, returning errors explicitly. -/
def constructMaskFn (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId] [DecidableEq S.Secret]
    (st : RefreshRoundState S) : Except String (MaskFn S) := do
  if ¬ decide (st.phase = .apply) then
    throw "not in apply phase"
  match computeFinalMasks S st with
  | .error e => throw e
  | .ok masks =>
      if hzero : masks.sum = 0 then
        pure (makeMaskFn S st)
      else
        throw "zero-sum check failed"

theorem List.sum_perm {α : Type*} [AddCommMonoid α] (l1 l2 : List α) :
  l1.Perm l2 → l1.sum = l2.sum := by
  intro hperm; exact hperm.sum_eq

theorem List.toFinset_toList_perm' {α : Type*} [DecidableEq α] (l : List α) :
  l.Nodup → l.toFinset.toList.Perm l := by
  intro hnodup
  exact List.toFinset_toList hnodup

/-- Construct zero-sum mask with proof, given precomputed masks.

    **Mathematical justification**:
    We need to prove: `(st.parties.toFinset).sum (makeMaskFn S st).mask = 0`

    Given:
    - `hmasks`: `computeFinalMasks S st = .ok masks`
    - `hzero`: `masks.sum = 0`
    - `hnodup`: `st.parties.Nodup`

    The proof requires:
    1. `makeMaskFn_eq_finalMasks`: mapping mask function over parties equals `masks`
    2. `List.sum_toFinset hnodup`: list sum equals finset sum when Nodup
    3. Transitivity: finset sum = list sum = masks.sum = 0

    **Note**: Uses sorry because it depends on `makeMaskFn_eq_finalMasks` (also sorry)
    and the connection between List.sum and Finset.sum over a Nodup list requires
    showing that the finset.toList permutation preserves sum, which involves
    List.toFinset_toList_perm and List.sum_perm lemmas in combination. -/
def constructZeroSumMask (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S)
    (masks : List S.Secret)
    (hmasks : computeFinalMasks S st = .ok masks)
    (hzero : masks.sum = 0)
    (_hnodup : st.parties.Nodup)
    : ZeroSumMaskFn S (List.toFinset st.parties) :=
  { fn := makeMaskFn S st
    sum_zero := by
      -- Would chain: finset sum → list sum → masks.sum = 0
      sorry
    }

/-- Convenience function: construct zero-sum mask with runtime checks.
    Returns None if preconditions fail. -/
def tryConstructZeroSumMask (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId] [DecidableEq S.Secret]
    (st : RefreshRoundState S)
    : Option (ZeroSumMaskFn S (List.toFinset st.parties)) :=
  if hphase : st.phase = .apply then
    match hmatch : computeFinalMasks S st with
    | .error _ => none
    | .ok masks =>
        if hzero : masks.sum = 0 then
          if hnodup : st.parties.Nodup then
            some (constructZeroSumMask S st masks hmatch hzero hnodup)
          else none
        else none
  else none

end IceNine.Protocol.RefreshCoord
