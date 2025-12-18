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

set_option autoImplicit false

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
  unfold checkPair verifyCommitmentOpening at h
  by_cases h1 : c.sender = r.sender
  · by_cases h2 : S.commit r.pk_i r.opening = c.commitPk
    · simp [h1, h2] at h; exact ⟨h1, h2⟩
    · simp [h1, h2] at h
  · simp [h1] at h

/-- Helper: forM on zipped list returning ok implies Forall₂.
    Induction on the lists, using checkPair_ok_pred at each step.
    Requires equal lengths since zip truncates silently on mismatch. -/
lemma forM_zip_ok_forall2
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (hlen : commits.length = reveals.length)
  (h : (List.zip commits reveals).forM (fun (c, r) => checkPair S c r) = Except.ok ()) :
  List.Forall₂ (fun c r => c.sender = r.sender ∧ S.commit r.pk_i r.opening = c.commitPk) commits reveals := by
  classical
  induction commits generalizing reveals with
  | nil =>
    cases reveals with
    | nil => exact List.Forall₂.nil
    | cons _ _ => cases hlen
  | cons c cs ih =>
    cases reveals with
    | nil => cases hlen
    | cons r rs =>
      have hlen' : cs.length = rs.length := by
        simpa using Nat.succ.inj hlen
      have h0 :
          (checkPair S c r >>= fun _ =>
              (List.zip cs rs).forM (fun (c, r) => checkPair S c r)) =
            Except.ok () := by
        have h' := h
        simp [List.zip_cons_cons, List.forM_cons] at h'
        exact h'
      cases hpair : checkPair S c r with
      | ok _ =>
        have hhead : c.sender = r.sender ∧ S.commit r.pk_i r.opening = c.commitPk :=
          checkPair_ok_pred (S := S) c r hpair
        have htail :
            (List.zip cs rs).forM (fun (c, r) => checkPair S c r) = Except.ok () := by
          simpa [hpair] using h0
        exact List.Forall₂.cons hhead (ih rs hlen' htail)
      | error _ =>
        cases (by simpa [hpair] using h0)

/-- checkPairs success → Forall₂ validity on pairs.
    Each commit/reveal pair has matching IDs and correct opening. -/
lemma checkPairs_ok_forall2
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (h : checkPairs S commits reveals = Except.ok ()) :
  List.Forall₂ (fun c r => c.sender = r.sender ∧ S.commit r.pk_i r.opening = c.commitPk) commits reveals := by
  -- Proof that checkPairs success implies validity on all pairs
  classical
  unfold checkPairs at h
  by_cases hlen : commits.length ≠ reveals.length
  · -- Length mismatch branch throws .lengthMismatch, so cannot be ok
    simp [hlen] at h
  · have hlen' : commits.length = reveals.length := not_not.mp hlen
    have hforM :
        (List.zip commits reveals).forM (fun (c, r) => checkPair S c r) = Except.ok () := by
      simpa [hlen] using h
    exact forM_zip_ok_forall2 (S := S) commits reveals hlen' hforM

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
  classical
  unfold dkgAggregateChecked at h
  by_cases hlen : commits.length = reveals.length
  · by_cases hdup : (reveals.map (·.sender)).Nodup
    · cases hcp : checkPairs S commits reveals with
      | ok _ =>
          -- success path: pk was bound from the final `pure`
          simp [hlen, hdup, hcp] at h
          exact h.symm
      | error _ =>
          -- impossible: ok result cannot arise from error
          simp [hlen, hdup, hcp] at h
    · -- duplicate parties case: computation throws, cannot be ok
      simp [hlen, hdup] at h
      cases h
  · -- length mismatch: computation throws, cannot be ok
    simp [hlen] at h
    cases h

/-- Ok result → dkgValid predicate holds.
    Uses checkPairs_ok_forall2 to establish the validity predicate. -/
lemma dkgAggregateChecked_ok_valid
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (pk : S.Public)
  (h : dkgAggregateChecked S commits reveals = Except.ok pk) :
  dkgValid S commits reveals := by
  classical
  unfold dkgAggregateChecked at h
  by_cases hlen : commits.length = reveals.length
  · by_cases hdup : (reveals.map (·.sender)).Nodup
    · cases hcp : checkPairs S commits reveals with
      | ok _ =>
          have hv : dkgValid S commits reveals :=
            checkPairs_ok_forall2 (S := S) commits reveals (by simpa using hcp)
          simpa [dkgValid] using hv
      | error _ =>
          simp [hlen, hdup, hcp] at h
    · simp [hlen, hdup] at h
      cases h
  · simp [hlen] at h
    cases h

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
  by_cases hlen : commits.length = reveals.length
  · simp [hlen] at h
    by_cases hcs : dkgCheckComplaints S commits reveals = []
    · simp [hcs] at h
      have hs : (reveals.map (·.pk_i)).sum = pk := by
        simpa [Except.ok.injEq] using h
      exact hs.symm
    · simp [hcs] at h
  · simp [hlen] at h

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
  split_ifs at h with hlen
  · simp only [Option.some.injEq] at h
    subst h
    simp [List.map_map]
  -- Negative branch (none = some tr) is impossible, automatically closed

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
  classical
  unfold dealerKeygen at h
  by_cases hlen : pids.length = secrets.length ∧ secrets.length = opens.length
  · simp [hlen] at h
    cases h with
    | refl =>
      -- Reduce to a property about nested zip construction.
      intro sh hmem
      let mkShare : S.PartyId × S.Secret × S.Opening → DealerShare S :=
        fun (pid, sk, op) =>
          let pk_i := S.A sk
          let com  := S.commit pk_i op
          { pid := pid, sk_i := sk, pk_i := pk_i, opening := op, commitPk := com }
      have hwf_zip :
         ∀ (ps : List S.PartyId) (ss : List S.Secret) (os : List S.Opening),
            ∀ sh, sh ∈ (ps.zip (ss.zip os)).map mkShare → DealerShare.wellFormed S sh := by
         intro ps ss os
         induction ps generalizing ss os with
         | nil =>
           intro sh hmem
           simp [List.zip] at hmem
         | cons pid ps ih =>
           intro sh hmem
           cases ss with
           | nil =>
             simp [List.zip] at hmem
           | cons sk ss' =>
             cases os with
             | nil =>
               simp [List.zip] at hmem
             | cons op os' =>
               simp only [List.zip_cons_cons, List.map_cons, List.mem_cons] at hmem
               cases hmem with
               | inl hEq =>
                 subst hEq
                 simp [DealerShare.wellFormed, mkShare]
               | inr hIn =>
                 exact ih ss' os' sh hIn
      have : sh ∈ (pids.zip (secrets.zip opens)).map mkShare := by
        simpa [mkShare] using hmem
      exact hwf_zip pids secrets opens sh this
  · have hfalse : False := by
      simp [hlen] at h
    cases hfalse

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
