/-
# Share repair protocol

We model a share repair protocol where a target party (who has lost its share)
asks a helper set to reconstruct its share. Each helper provides a masked delta
that lets the target reconstruct its share without revealing other shares.

The protocol uses Lagrange interpolation in the t-of-n case, or additive
reconstruction in the n-of-n case.
-/

import IceNine.Protocol.Core
import Mathlib

namespace IceNine.Protocol

open List

/-! ## Core Types -/

/-- Repair request from a party that lost its share. -/
structure RepairRequest (S : Scheme) :=
  (requester : S.PartyId)
  (knownPk_i : S.Public)  -- The public share is still known
deriving Repr

/-- Repair message from a helper to the requester. -/
structure RepairMsg (S : Scheme) :=
  (from   : S.PartyId)
  (to     : S.PartyId)
  (delta  : S.Secret)
deriving Repr

/-- Bundle of repair messages; lists can be merged via append. -/
structure RepairBundle (S : Scheme) :=
  (msgs : List (RepairMsg S))
deriving Repr

instance (S : Scheme) : Join (RepairBundle S) := ⟨fun a b => ⟨a.msgs ++ b.msgs⟩⟩

/-- Repair session state tracking the repair protocol progress. -/
structure RepairSession (S : Scheme) :=
  (request   : RepairRequest S)
  (helpers   : Finset S.PartyId)
  (received  : RepairBundle S)
  (threshold : Nat)
deriving Repr

instance (S : Scheme) : Join (RepairSession S) :=
  ⟨fun a b => { request   := a.request
              , helpers   := a.helpers ∪ b.helpers
              , received  := a.received ⊔ b.received
              , threshold := max a.threshold b.threshold }⟩

/-! ## Repair Protocol Functions -/

/-- Create a repair request for a lost share. -/
def createRepairRequest
  (S : Scheme)
  (pid : S.PartyId)
  (pk_i : S.Public)
  : RepairRequest S :=
  { requester := pid, knownPk_i := pk_i }

/-- Helper generates a delta contribution for the requester.
    In additive sharing, each helper j sends a share of its own contribution
    to reconstructing the target's share. -/
def helperContribution
  (S : Scheme)
  (helper : KeyShare S)
  (requester : S.PartyId)
  (coefficient : S.Scalar)
  : RepairMsg S :=
  { from  := helper.pid
  , to    := requester
  , delta := coefficient • helper.sk_i }

/--
  Combine helper deltas to repair a lost share.
  Assumes deltas are properly weighted so their sum equals the target share value.
-/
def repairShare
  (S : Scheme)
  (msgs : List (RepairMsg S))
  : S.Secret :=
  msgs.foldl (fun acc m => acc + m.delta) (0 : S.Secret)

/-- Filter messages to only those addressed to a specific party. -/
def messagesFor
  (S : Scheme) [DecidableEq S.PartyId]
  (msgs : List (RepairMsg S))
  (target : S.PartyId)
  : List (RepairMsg S) :=
  msgs.filter (fun m => m.to = target)

/-- Extract unique helper party IDs from a message list. -/
def helperPids
  (S : Scheme) [DecidableEq S.PartyId]
  (msgs : List (RepairMsg S))
  : List S.PartyId :=
  msgs.map (·.from) |>.dedup

/-! ## Verification Predicates -/

/-- Verify that a repaired share matches its known public share. -/
def verifyRepairedShare
  (S : Scheme)
  (repairedSk : S.Secret)
  (expectedPk : S.Public)
  : Prop :=
  S.A repairedSk = expectedPk

/-- Predicate: repair messages are well-formed (all addressed to the same target). -/
def repairMsgsWellFormed
  (S : Scheme) [DecidableEq S.PartyId]
  (msgs : List (RepairMsg S))
  (target : S.PartyId)
  : Prop :=
  ∀ m ∈ msgs, m.to = target

/-- Predicate: repair messages come from distinct helpers. -/
def repairMsgsDistinct
  (S : Scheme) [DecidableEq S.PartyId]
  (msgs : List (RepairMsg S))
  : Prop :=
  (msgs.map (·.from)).Nodup

/-! ## Threshold Repair -/

/-- Check if enough helpers have contributed. -/
def hasEnoughHelpers
  (S : Scheme) [DecidableEq S.PartyId]
  (session : RepairSession S)
  : Bool :=
  (helperPids S session.received.msgs).length ≥ session.threshold

/-- Attempt to complete repair if threshold is met. -/
def tryCompleteRepair
  (S : Scheme) [DecidableEq S.PartyId]
  (session : RepairSession S)
  : Option S.Secret :=
  if hasEnoughHelpers S session then
    some (repairShare S session.received.msgs)
  else
    none

end IceNine.Protocol
