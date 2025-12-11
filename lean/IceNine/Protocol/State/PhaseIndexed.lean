/-
# Type-Indexed Phase Transitions

Phase state machine where invalid transitions are compile-time errors.
The phase is encoded in the type, so `stepCommit` can only be called
when in `.commit` phase, producing a state in `.reveal` phase.

## Design Choice: List vs MsgMap

This module uses `List` for message storage rather than `MsgMap` (as in Phase.lean).
This is an intentional design decision with trade-offs:

### Why List here:

1. **Type-indexed focus**: The primary safety guarantee is phase correctness.
   The type `PhaseState S .commit` prevents calling reveal-phase functions.
   This is the main innovation of this module.

2. **Proof simplicity**: List operations have simpler lemmas in Mathlib.
   Proofs about phase transitions are easier with list semantics.

3. **Downstream flexibility**: Consumers can wrap messages in MsgMap if they
   need conflict-freedom, or work with lists directly if they don't.

4. **Completeness tracking**: Phase data tracks `expectedParties` count.
   Completeness is enforced by comparing list length to expected count.

### When to use MsgMap (Phase.lean) instead:

1. When you need CRDT merge semantics for network handling
2. When you want conflicts to be un-expressable at the type level
3. When building production networking code

### When to use PhaseIndexed:

1. When you want phase-transition safety as the primary guarantee
2. For security proofs where phase correctness is the key property
3. When you're building high-level protocol logic

## Benefits of Type-Indexed Phases

1. **Type Safety**: Impossible to call reveal processing in commit phase
2. **Documentation**: Type signatures show valid transitions
3. **Proof Obligations**: Phase proofs are automatic from types

This module provides an alternative to the runtime-checked Phase.lean.
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.State.Phase
import IceNine.Protocol.Sign.Sign
import Mathlib

namespace IceNine.Protocol.PhaseIndexed

open IceNine.Protocol

/-!
## Phase-Indexed State

State indexed by current phase. Each phase has different available data.
The type system prevents accessing data that doesn't exist yet.
-/

/-- Phase-indexed state: the phase parameter determines what data is available. -/
inductive PhaseState (S : Scheme) : Phase → Type where
  | commit  : CommitPhaseData S → PhaseState S .commit
  | reveal  : RevealPhaseData S → PhaseState S .reveal
  | shares  : SharePhaseData S → PhaseState S .shares
  | done    : DonePhaseData S → PhaseState S .done

/-- Data available in commit phase. -/
structure CommitPhaseData (S : Scheme) where
  /-- Commits received so far -/
  commits : List (DkgCommitMsg S)
  /-- Expected number of parties -/
  expectedParties : Nat
deriving Repr

/-- Data available in reveal phase (includes all commit data). -/
structure RevealPhaseData (S : Scheme) where
  /-- All commits (now complete) -/
  commits : List (DkgCommitMsg S)
  /-- Reveals received so far -/
  reveals : List (DkgRevealMsg S)
  /-- Proof that we have enough commits -/
  commitsComplete : commits.length = expectedParties
  /-- Expected parties count -/
  expectedParties : Nat
deriving Repr

/-- Data available in share phase (includes all reveal data). -/
structure SharePhaseData (S : Scheme) where
  /-- All commits -/
  commits : List (DkgCommitMsg S)
  /-- All reveals (now complete) -/
  reveals : List (DkgRevealMsg S)
  /-- Signature shares received so far -/
  shares : List (SignShareMsg S)
  /-- Active signers -/
  activeSigners : Finset S.PartyId
  /-- Message being signed -/
  message : S.Message
  /-- Threshold for completion -/
  threshold : Nat
deriving Repr

/-- Data available in done phase (final signature). -/
structure DonePhaseData (S : Scheme) where
  /-- Final aggregated signature -/
  signature : Sign.Signature S
  /-- Public key used -/
  publicKey : S.Public
  /-- Message signed -/
  message : S.Message
deriving Repr

/-!
## Phase Transition Functions

Each function takes a state in one phase and produces a state in the next phase.
The type signature enforces valid transitions.
-/

/-- Add a commit message in commit phase. Stays in commit phase. -/
def addCommit (S : Scheme)
    (st : PhaseState S .commit) (msg : DkgCommitMsg S)
    : PhaseState S .commit :=
  match st with
  | .commit data =>
      .commit { data with commits := msg :: data.commits }

/-- Check if ready to transition to reveal phase. -/
def canTransitionToReveal [DecidableEq S.PartyId]
    (data : CommitPhaseData S) : Bool :=
  data.commits.length = data.expectedParties

/-- Transition from commit to reveal phase (requires all commits). -/
def transitionToReveal (S : Scheme)
    (st : PhaseState S .commit)
    (hready : match st with
      | .commit data => data.commits.length = data.expectedParties)
    : PhaseState S .reveal :=
  match st, hready with
  | .commit data, h =>
      .reveal {
        commits := data.commits
        reveals := []
        commitsComplete := h
        expectedParties := data.expectedParties
      }

/-- Add a reveal message in reveal phase. Stays in reveal phase. -/
def addReveal (S : Scheme)
    (st : PhaseState S .reveal) (msg : DkgRevealMsg S)
    : PhaseState S .reveal :=
  match st with
  | .reveal data =>
      .reveal { data with reveals := msg :: data.reveals }

/-- Check if ready to transition to shares phase. -/
def canTransitionToShares [DecidableEq S.PartyId]
    (data : RevealPhaseData S) : Bool :=
  data.reveals.length = data.expectedParties

/-- Transition from reveal to shares phase (requires all reveals). -/
def transitionToShares (S : Scheme)
    (st : PhaseState S .reveal)
    (activeSigners : Finset S.PartyId)
    (message : S.Message)
    (threshold : Nat)
    (hready : match st with
      | .reveal data => data.reveals.length = data.expectedParties)
    : PhaseState S .shares :=
  match st, hready with
  | .reveal data, _ =>
      .shares {
        commits := data.commits
        reveals := data.reveals
        shares := []
        activeSigners := activeSigners
        message := message
        threshold := threshold
      }

/-- Add a signature share in shares phase. Stays in shares phase. -/
def addShare (S : Scheme)
    (st : PhaseState S .shares) (msg : SignShareMsg S)
    : PhaseState S .shares :=
  match st with
  | .shares data =>
      .shares { data with shares := msg :: data.shares }

/-- Check if ready to transition to done phase. -/
def canTransitionToDone [DecidableEq S.PartyId]
    (data : SharePhaseData S) : Bool :=
  data.shares.length ≥ data.threshold

/-- Transition from shares to done phase (requires threshold shares). -/
def transitionToDone (S : Scheme)
    (st : PhaseState S .shares)
    (aggregatedSig : Sign.Signature S)
    (publicKey : S.Public)
    (hready : match st with
      | .shares data => data.shares.length ≥ data.threshold)
    : PhaseState S .done :=
  match st, hready with
  | .shares data, _ =>
      .done {
        signature := aggregatedSig
        publicKey := publicKey
        message := data.message
      }

/-!
## Initial State

Start in commit phase with empty data.
-/

/-- Create initial state for a protocol run. -/
def initPhaseState (S : Scheme) (expectedParties : Nat) : PhaseState S .commit :=
  .commit {
    commits := []
    expectedParties := expectedParties
  }

/-!
## Phase Monotonicity

Type-level proof that phases only move forward.
-/

/-- Phase ordering: commit < reveal < shares < done. -/
def Phase.toNat : Phase → Nat
  | .commit => 0
  | .reveal => 1
  | .shares => 2
  | .done => 3

/-- Phase comparison. -/
instance : LT Phase where
  lt a b := a.toNat < b.toNat

instance : LE Phase where
  le a b := a.toNat ≤ b.toNat

/-- Decidable phase comparison. -/
instance : DecidableRel (α := Phase) (· < ·) :=
  fun a b => Nat.decLt a.toNat b.toNat

instance : DecidableRel (α := Phase) (· ≤ ·) :=
  fun a b => Nat.decLe a.toNat b.toNat

/-- transitionToReveal advances the phase. -/
theorem reveal_advances : Phase.commit < Phase.reveal := by
  simp [LT.lt, Phase.toNat]

/-- transitionToShares advances the phase. -/
theorem shares_advances : Phase.reveal < Phase.shares := by
  simp [LT.lt, Phase.toNat]

/-- transitionToDone advances the phase. -/
theorem done_advances : Phase.shares < Phase.done := by
  simp [LT.lt, Phase.toNat]

/-!
## Extraction Functions

Get data from phase states when needed.
-/

/-- Get commits from any phase that has them. -/
def getCommits (S : Scheme) : {p : Phase} → PhaseState S p → List (DkgCommitMsg S)
  | .commit, .commit data => data.commits
  | .reveal, .reveal data => data.commits
  | .shares, .shares data => data.commits
  | .done, .done _ => []  -- commits not stored in done phase

/-- Get reveals from phases that have them. -/
def getReveals (S : Scheme) : {p : Phase} → PhaseState S p → List (DkgRevealMsg S)
  | .commit, .commit _ => []
  | .reveal, .reveal data => data.reveals
  | .shares, .shares data => data.reveals
  | .done, .done _ => []

/-- Get shares from phases that have them. -/
def getShares (S : Scheme) : {p : Phase} → PhaseState S p → List (SignShareMsg S)
  | .commit, .commit _ => []
  | .reveal, .reveal _ => []
  | .shares, .shares data => data.shares
  | .done, .done _ => []

/-- Get final signature (only available in done phase). -/
def getSignature (S : Scheme) (st : PhaseState S .done) : Sign.Signature S :=
  match st with
  | .done data => data.signature

/-!
## Generic Message Processing

Process messages in a type-safe way based on current phase.
-/

/-- Message types that can be received. -/
inductive ProtocolMsg (S : Scheme) where
  | commitMsg : DkgCommitMsg S → ProtocolMsg S
  | revealMsg : DkgRevealMsg S → ProtocolMsg S
  | shareMsg : SignShareMsg S → ProtocolMsg S

/-- Process a commit message if in commit phase, otherwise no-op.
    Returns the state in an existential to handle phase flexibility. -/
def processCommitMsg (S : Scheme) (p : Phase)
    (st : PhaseState S p) (msg : DkgCommitMsg S)
    : Σ p', PhaseState S p' :=
  match p, st with
  | .commit, st' => ⟨.commit, addCommit S st' msg⟩
  | _, st' => ⟨p, st'⟩  -- ignore in other phases

/-- Process a reveal message if in reveal phase, otherwise no-op. -/
def processRevealMsg (S : Scheme) (p : Phase)
    (st : PhaseState S p) (msg : DkgRevealMsg S)
    : Σ p', PhaseState S p' :=
  match p, st with
  | .reveal, st' => ⟨.reveal, addReveal S st' msg⟩
  | _, st' => ⟨p, st'⟩

/-- Process a share message if in shares phase, otherwise no-op. -/
def processShareMsg (S : Scheme) (p : Phase)
    (st : PhaseState S p) (msg : SignShareMsg S)
    : Σ p', PhaseState S p' :=
  match p, st with
  | .shares, st' => ⟨.shares, addShare S st' msg⟩
  | _, st' => ⟨p, st'⟩

end IceNine.Protocol.PhaseIndexed
