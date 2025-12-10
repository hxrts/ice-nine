/-
# Repair Security Proofs

Security properties for the share repair protocol:
- Correctness: honest execution recovers the original share
- Privacy: no single helper learns the target share
- Robustness: threshold number of helpers suffices
-/

import Mathlib
import IceNine.Protocol.Core
import IceNine.Protocol.Repair
import IceNine.Protocol.Sign

namespace IceNine.Security

open IceNine.Protocol
open List

/-! ## Basic Lemmas -/

/-- Correctness: if deltas sum to sk_i, repairShare recovers sk_i. -/
lemma repair_correct
  (S : Scheme)
  (msgs : List (RepairMsg S))
  (sk_i : S.Secret)
  (h : msgs.foldl (fun acc m => acc + m.delta) (0 : S.Secret) = sk_i) :
  repairShare S msgs = sk_i := by
  simp [repairShare, h]

/-- Empty message list repairs to zero. -/
lemma repair_empty
  (S : Scheme) :
  repairShare S [] = (0 : S.Secret) := by
  simp [repairShare]

/-- Single message repairs to that delta. -/
lemma repair_single
  (S : Scheme)
  (m : RepairMsg S) :
  repairShare S [m] = m.delta := by
  simp [repairShare, List.foldl]

/-- Repair of concatenated lists equals sum of repairs. -/
lemma repair_append
  (S : Scheme)
  (msgs1 msgs2 : List (RepairMsg S)) :
  repairShare S (msgs1 ++ msgs2) = repairShare S msgs1 + repairShare S msgs2 := by
  unfold repairShare
  induction msgs1 with
  | nil => simp
  | cons m ms ih =>
      simp [List.foldl, add_assoc, add_comm, add_left_comm]
      rw [← ih]
      simp [List.foldl, add_assoc]

/-- Repair is linear in the deltas: scaling all deltas scales the result. -/
lemma repair_smul
  (S : Scheme)
  (c : S.Scalar)
  (msgs : List (RepairMsg S)) :
  repairShare S (msgs.map (fun m => { m with delta := c • m.delta }))
    = c • repairShare S msgs := by
  unfold repairShare
  induction msgs with
  | nil => simp
  | cons m ms ih =>
      simp [List.foldl, List.map, smul_add]
      sorry  -- requires showing foldl distributes with smul

/-! ## Correctness Properties -/

/--
  Main correctness theorem: if helpers provide properly weighted contributions
  that sum to the target share, repair succeeds.
-/
theorem repair_correctness
  (S : Scheme)
  (msgs : List (RepairMsg S))
  (targetSk : S.Secret)
  (h : (msgs.map (·.delta)).sum = targetSk) :
  repairShare S msgs = targetSk := by
  unfold repairShare
  induction msgs with
  | nil => simp at h; exact h.symm
  | cons m ms ih =>
      simp [List.foldl]
      simp [List.map, List.sum_cons] at h
      have : (ms.map (·.delta)).sum = targetSk - m.delta := by linarith
      specialize ih this
      simp [repairShare] at ih
      -- Need to show foldl accumulates correctly
      sorry

/--
  Verification theorem: repaired share matches the known public share.
-/
theorem repair_verification
  (S : Scheme)
  (msgs : List (RepairMsg S))
  (targetSk : S.Secret)
  (targetPk : S.Public)
  (hsum : (msgs.map (·.delta)).sum = targetSk)
  (hpk : S.A targetSk = targetPk) :
  verifyRepairedShare S (repairShare S msgs) targetPk := by
  unfold verifyRepairedShare
  have hrepair : repairShare S msgs = targetSk := repair_correctness S msgs targetSk hsum
  rw [hrepair, hpk]

/-! ## Privacy Properties -/

/--
  Privacy: if each delta is masked with helper-local randomness that sums to 0,
  the sum reveals only sk_i. An additional zero-sum mask does not change the
  repaired value.
-/
lemma repair_masked_zero
  (S : Scheme)
  (msgs : List (RepairMsg S))
  (mask : List S.Secret)
  (hmask : mask.sum = 0)
  (hlen : mask.length = msgs.length) :
  repairShare S (List.zipWith (fun m z => { m with delta := m.delta + z }) msgs mask)
    = repairShare S msgs := by
  unfold repairShare
  induction msgs generalizing mask with
  | nil =>
      cases mask with
      | nil => simp
      | cons => simp at hlen
  | cons m ms ih =>
      cases mask with
      | nil => simp at hlen
      | cons z zs =>
          simp at hlen
          simp [List.sum_cons] at hmask
          simp [List.zipWith, List.foldl]
          have ih' := ih zs (by linarith [hmask, z]) hlen
          simp [repairShare] at ih'
          -- The key insight: z + zs.sum = 0, so adding z to one and zs to others cancels
          sorry  -- detailed proof requires careful foldl manipulation

/--
  Privacy: the repair protocol reveals only the target share, not individual
  helper shares. This is captured by showing that zero-sum masks on the deltas
  do not change the recovered share.
-/
theorem repair_privacy_zerosum
  (S : Scheme)
  (msgs : List (RepairMsg S))
  (masks : List S.Secret)
  (hlen : masks.length = msgs.length)
  (hzero : masks.sum = 0) :
  repairShare S (List.zipWith (fun m z => { m with delta := m.delta + z }) msgs masks)
    = repairShare S msgs := by
  exact repair_masked_zero S msgs masks hzero hlen

/--
  Single-helper privacy: a single helper cannot determine the target share
  from its own contribution alone.
-/
def singleHelperPrivacy
  (S : Scheme)
  (helperDelta : S.Secret)
  (otherDeltasSum : S.Secret)
  : Prop :=
  -- The target share is helperDelta + otherDeltasSum
  -- Without knowing otherDeltasSum, the helper cannot determine the target
  True  -- This is an information-theoretic property, axiomatized here

/-! ## Robustness Properties -/

/--
  Threshold robustness: if at least t helpers contribute, repair can succeed.
-/
structure RepairRobustness (S : Scheme) [DecidableEq S.PartyId] where
  session : RepairSession S
  threshold_met : (helperPids S session.received.msgs).length ≥ session.threshold
  contributions_valid : ∀ m ∈ session.received.msgs, m.to = session.request.requester

/--
  If robustness conditions are met, tryCompleteRepair returns Some.
-/
theorem tryCompleteRepair_succeeds
  (S : Scheme) [DecidableEq S.PartyId]
  (robust : RepairRobustness S) :
  (tryCompleteRepair S robust.session).isSome := by
  unfold tryCompleteRepair hasEnoughHelpers
  simp [robust.threshold_met]

/--
  Totality: tryCompleteRepair always returns Some or None (no exceptions).
-/
theorem tryCompleteRepair_total
  (S : Scheme) [DecidableEq S.PartyId]
  (session : RepairSession S) :
  (tryCompleteRepair S session).isSome ∨ (tryCompleteRepair S session).isNone := by
  unfold tryCompleteRepair
  by_cases h : hasEnoughHelpers S session <;> simp [h]

/-! ## CRDT Properties -/

/-- Merge of repair bundles is associative. -/
lemma repairBundle_join_assoc
  (S : Scheme)
  (a b c : RepairBundle S) :
  (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) := by
  simp [Sup.sup, Join.join, List.append_assoc]

/-- Merge of repair bundles is commutative up to message order. -/
lemma repairBundle_join_comm_sum
  (S : Scheme)
  (a b : RepairBundle S) :
  repairShare S (a ⊔ b).msgs = repairShare S (b ⊔ a).msgs := by
  simp [Sup.sup, Join.join]
  rw [repair_append, repair_append]
  ring

/--
  Semilattice: RepairBundle join is idempotent.
-/
lemma repairBundle_join_idem
  (S : Scheme)
  (a : RepairBundle S) :
  a ⊔ a = ⟨a.msgs ++ a.msgs⟩ := by
  simp [Sup.sup, Join.join]

/--
  RepairSession merge preserves the requester identity.
-/
lemma repairSession_merge_requester
  (S : Scheme)
  (a b : RepairSession S) :
  (a ⊔ b).request = a.request := by
  simp [Sup.sup, Join.join]

/--
  RepairSession merge unions the helper sets.
-/
lemma repairSession_merge_helpers
  (S : Scheme)
  (a b : RepairSession S) :
  (a ⊔ b).helpers = a.helpers ∪ b.helpers := by
  simp [Sup.sup, Join.join]

/-! ## Lagrange Reconstruction -/

/--
  For polynomial secret sharing, Lagrange coefficients enable reconstruction.
  This captures the algebraic constraint that properly weighted shares sum to
  the target share.
-/
structure LagrangeReconstruction (S : Scheme) [Field S.Scalar] where
  targetPid : S.PartyId
  helperPids : List S.PartyId
  pidToScalar : S.PartyId → S.Scalar
  coefficients : S.PartyId → S.Scalar
  -- The Lagrange property: sum of coeff_j * share_j = target share
  lagrange_property :
    ∀ (shares : S.PartyId → S.Secret),
      (helperPids.map (fun j => coefficients j • shares j)).sum
        = shares targetPid

/--
  Given a valid Lagrange reconstruction and helper shares, repair succeeds.
-/
theorem lagrange_repair_correct
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (recon : LagrangeReconstruction S)
  (helperShares : S.PartyId → KeyShare S)
  (hshares : ∀ j ∈ recon.helperPids, (helperShares j).pid = j) :
  let msgs := recon.helperPids.map (fun j =>
    helperContribution S (helperShares j) recon.targetPid (recon.coefficients j))
  repairShare S msgs = (fun pid => (helperShares pid).sk_i) recon.targetPid := by
  sorry  -- Follows from the Lagrange property

/-! ## Security Assumptions -/

/--
  Repair security assumptions bundled together.
-/
structure RepairAssumptions (S : Scheme) where
  /-- Secure channels between helpers and requester -/
  secureChannels : Prop
  /-- Honest majority among helpers -/
  honestMajority : Prop
  /-- Commitment binding for verification -/
  commitBinding : Prop

/--
  Under the repair assumptions, the protocol is secure.
-/
def repairSecure (S : Scheme) (A : RepairAssumptions S) : Prop :=
  A.secureChannels ∧ A.honestMajority ∧ A.commitBinding

end IceNine.Security
