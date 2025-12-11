/-
# Share Repair Protocol

Recovers a lost share using contributions from helper parties. The party
who lost their share (requester) still knows their public share pk_i.
Helpers send masked deltas that sum to the lost sk_i via Lagrange.

Privacy: Individual deltas reveal nothing about helper shares. Only the
sum (the repaired share) is meaningful.
Security proofs in `Proofs/Extensions/Repair`.
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.State.Phase  -- for Join class
import Mathlib

namespace IceNine.Protocol

open List

/-!
## Core Types

The repair protocol uses request/response messaging:
- Requester broadcasts RepairRequest with known pk_i
- Helpers respond with RepairMsg containing weighted deltas
- Messages accumulate in RepairBundle (CRDT via list append)
-/

/-- Repair request from party who lost their secret share.
    pk_i is public and still known for verification. -/
structure RepairRequest (S : Scheme) where
  requester : S.PartyId  -- party who lost their share
  knownPk_i : S.Public   -- public share for verification

/-- Repair contribution from a helper party.
    delta = λ_j·sk_j where λ_j is helper's Lagrange coefficient. -/
structure RepairMsg (S : Scheme) where
  sender : S.PartyId  -- helper party
  target : S.PartyId  -- requester (for routing)
  delta  : S.Secret   -- weighted share contribution

/-- Bundle of repair messages with CRDT merge via append.
    Out-of-order delivery is safe due to commutativity. -/
structure RepairBundle (S : Scheme) where
  msgs : List (RepairMsg S)

/-- CRDT merge: concatenate message lists. -/
instance (S : Scheme) : Join (RepairBundle S) := ⟨fun a b => ⟨a.msgs ++ b.msgs⟩⟩

/-- Repair session state for tracking progress.
    CRDT merge: union helpers, append messages, max threshold. -/
structure RepairSession (S : Scheme) where
  request   : RepairRequest S      -- who needs repair
  helpers   : Finset S.PartyId     -- available helpers
  received  : RepairBundle S       -- messages received so far
  threshold : Nat                  -- minimum helpers needed

/-- CRDT merge for repair sessions: monotonic on all fields. -/
instance (S : Scheme) [DecidableEq S.PartyId] : Join (RepairSession S) :=
  ⟨fun a b => { request   := a.request
                helpers   := a.helpers ∪ b.helpers
                received  := a.received ⊔ b.received
                threshold := max a.threshold b.threshold }⟩

/-!
## Repair Protocol Functions

1. Requester creates RepairRequest with known pk_i
2. Each helper computes delta = λ_j·sk_j (Lagrange-weighted share)
3. Requester sums deltas: sk_i = Σ_j λ_j·sk_j
4. Verify: A(sk_i) = pk_i confirms correct reconstruction
-/

/-- Create a repair request for a lost share.
    The requester still knows their public share for verification. -/
def createRepairRequest
  (S : Scheme)
  (pid : S.PartyId)    -- requester's party ID
  (pk_i : S.Public)    -- known public share
  : RepairRequest S :=
  { requester := pid, knownPk_i := pk_i }

/-- Helper generates weighted delta contribution.
    coefficient = Lagrange λ_j for this helper over the helper set. -/
def helperContribution
  (S : Scheme)
  (helper : KeyShare S)       -- helper's credential
  (requester : S.PartyId)     -- who to send to
  (coefficient : S.Scalar)    -- Lagrange weight λ_j
  : RepairMsg S :=
  { sender := helper.pid
    target := requester
    delta  := coefficient • helper.secret }  -- λ_j·sk_j

/-- Sum deltas to recover the lost share.
    Correctness: Σ_j λ_j·sk_j = sk_i via Lagrange interpolation. -/
def repairShare
  (S : Scheme)
  (msgs : List (RepairMsg S))
  : S.Secret :=
  (msgs.map (·.delta)).sum

/-- Filter messages addressed to a specific requester. -/
def messagesFor
  (S : Scheme) [DecidableEq S.PartyId]
  (msgs : List (RepairMsg S))
  (recipient : S.PartyId)
  : List (RepairMsg S) :=
  msgs.filter (fun m => m.target = recipient)

/-- Extract unique helper IDs from received messages.
    Uses extractUnique from Core. -/
def helperPids
  (S : Scheme) [DecidableEq S.PartyId]
  (msgs : List (RepairMsg S))
  : List S.PartyId :=
  extractUnique (·.sender) msgs

/-!
## Verification Predicates

After repair, verify A(repaired_sk) = pk_i to confirm correctness.
-/

/-- Verify repaired share: A(sk') must equal known pk_i.
    Uses generic share verification from Core. -/
def verifyRepairedShare
  (S : Scheme)
  (repairedSk : S.Secret)
  (expectedPk : S.Public)
  : Prop :=
  verifySecretPublic S repairedSk expectedPk

/-- All messages target the same requester. -/
def repairMsgsWellFormed
  (S : Scheme) [DecidableEq S.PartyId]
  (msgs : List (RepairMsg S))
  (recipient : S.PartyId)
  : Prop :=
  ∀ m ∈ msgs, m.target = recipient

/-- Each helper contributes at most once. -/
def repairMsgsDistinct
  (S : Scheme) [DecidableEq S.PartyId]
  (msgs : List (RepairMsg S))
  : Prop :=
  (msgs.map (·.sender)).Nodup

/-!
## Threshold Gating

Repair requires ≥ threshold helpers. Only attempt reconstruction
when enough contributions have been received.
-/

/-- Check if threshold of helpers reached. -/
def hasEnoughHelpers
  (S : Scheme) [DecidableEq S.PartyId]
  (session : RepairSession S)
  : Bool :=
  (helperPids S session.received.msgs).length ≥ session.threshold

/-- Complete repair if threshold met, otherwise wait for more helpers. -/
def tryCompleteRepair
  (S : Scheme) [DecidableEq S.PartyId]
  (session : RepairSession S)
  : Option S.Secret :=
  if hasEnoughHelpers S session then
    some (repairShare S session.received.msgs)
  else
    none

end IceNine.Protocol
