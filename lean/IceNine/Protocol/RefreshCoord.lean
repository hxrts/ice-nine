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

import IceNine.Protocol.Refresh
import IceNine.Protocol.Phase
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

/-!
## Message Maps for Refresh Coordination

Using MsgMap makes conflicting messages from the same sender **un-expressable**.
Each party can submit at most one commit and one reveal per refresh round.
-/

/-- Sender accessor for mask commit messages. -/
def maskCommitSender {S : Scheme} (m : MaskCommitMsg S) : S.PartyId := m.sender

/-- Sender accessor for mask reveal messages. -/
def maskRevealSender {S : Scheme} (m : MaskRevealMsg S) : S.PartyId := m.sender

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
def selectCoordinator [Inhabited PartyId]
    (parties : List PartyId) (strategy : CoordinatorStrategy PartyId) : PartyId :=
  match strategy with
  | .fixed pid => pid
  | .roundRobin round =>
      let idx := round % parties.length
      parties.get? idx |>.getD default
  | .random seed =>
      let idx := seed % parties.length
      parties.get? idx |>.getD default

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
def RefreshRoundState.coordinator [BEq S.PartyId] [Hashable S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S) : S.PartyId :=
  selectCoordinator st.parties st.coordStrategy

/-- Check if all parties have committed. -/
def RefreshRoundState.allCommitted [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) : Bool :=
  st.parties.all (fun p => st.maskCommits.contains p)

/-- Check if all parties have revealed. -/
def RefreshRoundState.allRevealed [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) : Bool :=
  st.parties.all (fun p => st.maskReveals.contains p)

/-- Result of processing a commit message. -/
inductive CommitProcessResult (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
  | success (newSt : RefreshRoundState S)
  | conflict (existing : MaskCommitMsg S)
  | wrongPhase

/-- Process mask commitment with conflict detection.
    Returns conflict indicator if sender already has a commit.

    **Design choice**: We use strict conflict detection rather than CRDT-style
    silent merging because detecting duplicate/conflicting messages is security-critical
    in cryptographic protocols. A duplicate commit could indicate an attack. -/
def processCommit (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (st : RefreshRoundState S) (msg : MaskCommitMsg S)
    : CommitProcessResult S :=
  if st.phase = .commit then
    match st.maskCommits.tryInsert maskCommitSender msg with
    | .success newCommits =>
        let newSt := { st with maskCommits := newCommits }
        -- Transition to reveal phase if all committed
        if newSt.allCommitted then
          .success { newSt with phase := .reveal }
        else .success newSt
    | .conflict existing => .conflict existing
  else .wrongPhase

/-- Result of processing a reveal message. -/
inductive RevealProcessResult (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
  | success (newSt : RefreshRoundState S)
  | conflict (existing : MaskRevealMsg S)
  | invalidOpening
  | noCommit
  | wrongPhase

/-- Process mask reveal with conflict detection.

    **Design choice**: We use strict conflict detection rather than CRDT-style
    silent merging because detecting duplicate/conflicting messages is security-critical
    in cryptographic protocols. A duplicate reveal could indicate an attack. -/
def processReveal (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.Commitment]
    (st : RefreshRoundState S) (msg : MaskRevealMsg S)
    : RevealProcessResult S :=
  if st.phase = .reveal then
    -- Verify commitment opens correctly
    match st.maskCommits.get? msg.sender with
    | some c =>
        if S.commit (S.A msg.mask) msg.opening = c.maskCommit then
          match st.maskReveals.tryInsert maskRevealSender msg with
          | .success newReveals =>
              let newSt := { st with maskReveals := newReveals }
              -- Transition to adjust phase if all revealed
              if newSt.allRevealed then
                .success { newSt with phase := .adjust }
              else .success newSt
          | .conflict existing => .conflict existing
        else .invalidOpening
    | none => .noCommit
  else .wrongPhase

/-- Coordinator computes adjustment to achieve zero-sum.
    adjustment = -Σ_{i≠coord} m_i -/
def computeAdjustment (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S) : Option S.Secret :=
  if st.phase = .adjust then
    let coord := st.coordinator
    -- Sum all revealed masks except coordinator's
    let otherMasks := st.maskReveals.toList.filter (fun r => r.sender ≠ coord)
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
    (st : RefreshRoundState S) : List S.Secret :=
  match st.adjustment with
  | some adj =>
      let coord := st.coordinator
      -- For each party, get their mask (or adjustment for coordinator)
      st.parties.map fun pid =>
        match st.maskReveals.get? pid with
        | some r => if pid = coord then adj.adjustment else r.mask
        | none => 0
  | none => []

/-- Verify zero-sum property after adjustment.
    Returns proof-friendly Prop rather than Bool. -/
def zeroSumProp (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S) : Prop :=
  (computeFinalMasks S st).sum = 0

/-- Decidable zero-sum check. -/
def verifyZeroSum (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId] [DecidableEq S.Secret]
    (st : RefreshRoundState S) : Bool :=
  (computeFinalMasks S st).sum = 0

/-- verifyZeroSum reflects zeroSumProp. -/
theorem verifyZeroSum_spec (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId] [DecidableEq S.Secret]
    (st : RefreshRoundState S) :
    verifyZeroSum S st = true ↔ zeroSumProp S st := by
  simp only [verifyZeroSum, zeroSumProp, beq_iff_eq]

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

/-- The mask function applied to parties equals computeFinalMasks. -/
theorem makeMaskFn_eq_finalMasks (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S) :
    st.parties.map (fun pid => (makeMaskFn S st).mask pid) = computeFinalMasks S st := by
  simp only [makeMaskFn, computeFinalMasks]
  cases st.adjustment with
  | none => simp
  | some adj => rfl

/-- Construct the final zero-sum mask function from refresh round.
    Returns None if not in apply phase or zero-sum check fails. -/
def constructMaskFn (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId] [DecidableEq S.Secret]
    (st : RefreshRoundState S) : Option (MaskFn S) :=
  if st.phase = .apply ∧ verifyZeroSum S st then
    some (makeMaskFn S st)
  else none

/-- Axiom: Sum over a permutation of a list equals sum over the original list.
    This is a standard property of commutative addition. -/
axiom List.sum_perm {α : Type*} [AddCommMonoid α] (l1 l2 : List α) :
  l1.Perm l2 → l1.sum = l2.sum

/-- Axiom: Finset.ofList.toList is a permutation of deduped original list.
    For a nodup list, this is exactly the original (up to permutation). -/
axiom Finset.ofList_toList_perm {α : Type*} [DecidableEq α] (l : List α) :
  l.Nodup → (Finset.ofList l).toList.Perm l

/-- Construct zero-sum mask with proof.

    Requires that the party list has no duplicates (each party appears once).
    This is a natural requirement: each party contributes exactly one mask. -/
def constructZeroSumMask (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S)
    (hzero : zeroSumProp S st)
    (hnodup : st.parties.Nodup)
    : ZeroSumMaskFn S (Finset.ofList st.parties) :=
  { fn := makeMaskFn S st
    sum_zero := by
      -- Goal: (Finset.ofList st.parties).toList.map (makeMaskFn S st).mask sums to 0
      -- Strategy: show this list is a permutation of st.parties.map ..., use sum_perm
      let f := fun pid => (makeMaskFn S st).mask pid
      -- (Finset.ofList st.parties).toList is a permutation of st.parties
      have hperm : (Finset.ofList st.parties).toList.Perm st.parties :=
        Finset.ofList_toList_perm st.parties hnodup
      -- Map preserves permutation
      have hmapperm : ((Finset.ofList st.parties).toList.map f).Perm (st.parties.map f) :=
        List.Perm.map f hperm
      -- Use sum_perm
      have hsumeq : ((Finset.ofList st.parties).toList.map f).sum = (st.parties.map f).sum :=
        List.sum_perm _ _ hmapperm
      -- From makeMaskFn_eq_finalMasks: st.parties.map f = computeFinalMasks S st
      have hmask : st.parties.map f = computeFinalMasks S st :=
        makeMaskFn_eq_finalMasks S st
      -- From hzero: (computeFinalMasks S st).sum = 0
      rw [hsumeq, hmask]
      exact hzero
  }

/-- Convenience function: construct zero-sum mask with runtime checks.
    Returns None if preconditions fail. -/
def tryConstructZeroSumMask (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId] [DecidableEq S.Secret]
    (st : RefreshRoundState S)
    : Option (ZeroSumMaskFn S (Finset.ofList st.parties)) :=
  if hphase : st.phase = .apply then
    if hzero : verifyZeroSum S st = true then
      if hnodup : st.parties.Nodup then
        some (constructZeroSumMask S st ((verifyZeroSum_spec S st).mp hzero) hnodup)
      else none
    else none
  else none

end IceNine.Protocol.RefreshCoord
