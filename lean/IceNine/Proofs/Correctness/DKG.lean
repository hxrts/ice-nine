/-
# DKG Security Proofs

Correctness and robustness for Distributed Key Generation:
- Happy-path: valid reveals produce correct global public key
- Soundness: checked aggregation implies validity predicate
- Completeness: totality of aggregation functions
- Dealer properties: binding between commitment and public share
-/

import IceNine.Protocol.DKG.Core
import IceNine.Protocol.DKG.Threshold
import IceNine.Protocol.DKG.Dealer
import IceNine.Proofs.Core.ListLemmas

namespace IceNine.Proofs.Correctness.DKG

open IceNine.Protocol
open List

/-!
## Happy-Path Correctness

When all parties behave honestly (dkgValid holds), aggregation succeeds
and produces pk = Σ pk_i.
-/

/-- Valid transcript → aggregation succeeds with correct pk.
    pk = Σ pk_i is the sum of all public shares. -/
lemma dkgAggregate_correct
  (S : Scheme)
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (_h : dkgValid S commits reveals) :
  dkgAggregate S reveals = (reveals.map (·.pk_i)).sum := by
  rfl

/-!
## Soundness Lemmas

Checked aggregation (Ok result) implies the validity predicate.
-/

/-- Helper: checkPair success implies the validity predicate.
    Extract the two conditions from a successful checkPair call. -/
lemma checkPair_ok_pred
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (c : DkgCommitMsg S) (r : DkgRevealMsg S)
  (h : checkPair S c r = Except.ok ()) :
  c.sender = r.sender ∧ S.commit r.pk_i r.opening = c.commitPk := by
  simp only [checkPair, verifyCommitmentOpening] at h
  split_ifs at h with h1 h2 h3
  · exact ⟨h1, h2⟩
  all_goals simp at h

/-- Helper: forM on zipped list returning ok implies Forall₂.
    Induction on the lists, using checkPair_ok_pred at each step. -/
lemma forM_zip_ok_forall2
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (h : (List.zip commits reveals).forM (fun (c, r) => checkPair S c r) = Except.ok ()) :
  List.Forall₂ (fun c r => c.sender = r.sender ∧ S.commit r.pk_i r.opening = c.commitPk) commits reveals := by
  induction commits generalizing reveals with
  | nil =>
    cases reveals with
    | nil => exact List.Forall₂.nil
    | cons _ _ => simp [List.zip] at h; exact List.Forall₂.nil
  | cons c cs ih =>
    cases reveals with
    | nil => simp [List.zip] at h; exact List.Forall₂.nil
    | cons r rs =>
      simp only [List.zip_cons_cons, List.forM_cons] at h
      -- h : checkPair S c r >>= (fun _ => forM ...) = Except.ok ()
      cases hcp : checkPair S c r with
      | error e => simp [hcp] at h
      | ok _ =>
        simp [hcp] at h
        exact List.Forall₂.cons (checkPair_ok_pred S c r hcp) (ih rs h)

/-- checkPairs success → Forall₂ validity on pairs.
    Each commit/reveal pair has matching IDs and correct opening. -/
lemma checkPairs_ok_forall2
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (h : checkPairs S commits reveals = Except.ok ()) :
  List.Forall₂ (fun c r => c.sender = r.sender ∧ S.commit r.pk_i r.opening = c.commitPk) commits reveals := by
  simp only [checkPairs] at h
  split_ifs at h with hlen
  · simp at h
  · exact forM_zip_ok_forall2 S commits reveals h

/-- Checked aggregation is total: always Ok or Error. -/
lemma dkgAggregateChecked_total
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S)) :
  (∃ pk, dkgAggregateChecked S commits reveals = Except.ok pk) ∨
  (∃ e, dkgAggregateChecked S commits reveals = Except.error e) := by
  cases h : dkgAggregateChecked S commits reveals with
  | ok pk => left; exact ⟨pk, rfl⟩
  | error e => right; exact ⟨e, rfl⟩

/-- Ok result → pk equals sum of public shares.
    The returned pk is exactly the sum of revealed public shares. -/
lemma dkgAggregateChecked_sound
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (pk : S.Public)
  (h : dkgAggregateChecked S commits reveals = Except.ok pk) :
  pk = (reveals.map (·.pk_i)).sum := by
  unfold dkgAggregateChecked at h
  split_ifs at h with hlen hdup
  · -- Both checks passed, now we need to extract the result
    cases hcheck : checkPairs S commits reveals with
    | error e => simp [hcheck] at h
    | ok _ =>
      simp [hcheck] at h
      exact h.symm
  · simp at h
  · simp at h

/-- Ok result → dkgValid predicate holds.
    Uses checkPairs_ok_forall2 to establish the validity predicate. -/
lemma dkgAggregateChecked_ok_valid
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (pk : S.Public)
  (h : dkgAggregateChecked S commits reveals = Except.ok pk) :
  dkgValid S commits reveals := by
  unfold dkgAggregateChecked at h
  split_ifs at h with hlen hdup
  · -- Both checks passed
    cases hcheck : checkPairs S commits reveals with
    | error e => simp [hcheck] at h
    | ok _ =>
      -- checkPairs succeeded, so dkgValid holds
      exact checkPairs_ok_forall2 S commits reveals hcheck
  · simp at h
  · simp at h

/-!
## Complaint-Based Aggregation

With complaints, Ok result still implies correct pk.
-/

/-- Ok from complaint-based aggregation → correct pk.
    When no complaints are raised, pk equals sum of public shares. -/
lemma dkgAggregateWithComplaints_correct
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  [Inhabited S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (pk : S.Public)
  (h : dkgAggregateWithComplaints S commits reveals = Except.ok pk) :
  pk = (reveals.map (·.pk_i)).sum := by
  simp only [dkgAggregateWithComplaints] at h
  split_ifs at h with hlen hempty
  · -- Length matched and no complaints: pk is explicitly set to sum
    simp only [Except.ok.injEq] at h
    exact h.symm
  · -- Complaints exist: returns error, contradicts h
    simp at h
  · -- Length mismatch: returns error, contradicts h
    simp at h

/-!
## Dealer Properties

Trusted dealer produces consistent outputs.
-/

/-- Dealer's pk equals sum of share public keys. -/
lemma dealerKeygen_pk
  (S : Scheme)
  {pids : List S.PartyId} {secrets : List S.Secret} {opens : List S.Opening}
  {tr : DealerTranscript S}
  (h : dealerKeygen S pids secrets opens = some tr) :
  tr.pk = (tr.shares.map (·.pk_i)).sum := by
  unfold dealerKeygen at h
  by_cases hlen : pids.length = secrets.length ∧ secrets.length = opens.length
  · simp [hlen] at h; cases h with | refl => rfl
  · simp [hlen] at h

/-- Well-formed dealer share: commitPk is actually a commitment to pk_i.
    This holds for all shares produced by dealerKeygen. -/
def DealerShare.wellFormed (S : Scheme) (sh : DealerShare S) : Prop :=
  sh.commitPk = S.commit sh.pk_i sh.opening

/-- Shares from dealerKeygen are well-formed.
    Follows directly from the construction in dealerKeygen. -/
lemma dealerKeygen_wellFormed
  (S : Scheme)
  {pids : List S.PartyId} {secrets : List S.Secret} {opens : List S.Opening}
  {tr : DealerTranscript S}
  (h : dealerKeygen S pids secrets opens = some tr) :
  ∀ sh ∈ tr.shares, DealerShare.wellFormed S sh := by
  unfold dealerKeygen at h
  split_ifs at h with hlen
  · simp only [Option.some.injEq] at h
    cases h
    -- shares are constructed with commitPk := S.commit pk_i op
    intro sh hsh
    unfold DealerShare.wellFormed
    -- sh is in the zipWith3 result - use our custom membership lemma
    obtain ⟨i, _, pid, sk, op, hpid, hsk, hop, hsh_eq⟩ := List.mem_zipWith3 hsh
    -- The share was constructed as: { commitPk := S.commit (S.A sk) op, pk_i := S.A sk, opening := op, ... }
    simp only [getElem?_eq_some_iff] at hpid hsk hop
    obtain ⟨_, hpid'⟩ := hpid
    obtain ⟨_, hsk'⟩ := hsk
    obtain ⟨_, hop'⟩ := hop
    -- Substitute into hsh_eq to see the structure
    simp only [← hsh_eq]
    rfl
  · simp at h

/-- Binding: same commitment → same public key (for well-formed shares).
    Uses scheme's commitBinding property. -/
lemma dealer_commit_binding
  (S : Scheme)
  {sh1 sh2 : DealerShare S}
  (hwf1 : DealerShare.wellFormed S sh1)
  (hwf2 : DealerShare.wellFormed S sh2)
  (h : sh1.commitPk = sh2.commitPk) :
  sh1.pk_i = sh2.pk_i := by
  -- Both commitPk are actual commitments to their pk_i values
  unfold DealerShare.wellFormed at hwf1 hwf2
  -- sh1.commitPk = S.commit sh1.pk_i sh1.opening
  -- sh2.commitPk = S.commit sh2.pk_i sh2.opening
  -- sh1.commitPk = sh2.commitPk
  -- So: S.commit sh1.pk_i sh1.opening = S.commit sh2.pk_i sh2.opening
  have heq : S.commit sh1.pk_i sh1.opening = S.commit sh2.pk_i sh2.opening := by
    rw [← hwf1, ← hwf2, h]
  -- By commitment binding: sh1.pk_i = sh2.pk_i
  exact S.commitBinding heq

end IceNine.Proofs.Correctness.DKG
