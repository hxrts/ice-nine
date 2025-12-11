/-
# DKG Security Proofs

Correctness and robustness for Distributed Key Generation:
- Happy-path: valid reveals produce correct global public key
- Soundness: checked aggregation implies validity predicate
- Completeness: totality of aggregation functions
- Dealer properties: binding between commitment and public share
-/

import IceNine.Protocol.DKGCore
import IceNine.Protocol.DKGThreshold
import IceNine.Protocol.Dealer

namespace IceNine.Security.DKG

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
  (h : dkgValid S commits reveals) :
  dkgAggregate S commits reveals = some ((reveals.map (·.pk_i)).sum) := by
  simp [dkgAggregate, h]

/-!
## Soundness Lemmas

Checked aggregation (Ok result) implies the validity predicate.
-/

/-- checkPairs success → Forall2 validity on pairs.
    Each commit/reveal pair has matching IDs and correct opening. -/
lemma checkPairs_ok_forall2
  (S : Scheme)
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (h : checkPairs S commits reveals = Except.ok ()) :
  List.Forall2 (fun c r => c.sender = r.sender ∧ S.commit r.pk_i r.opening = c.commitPk) commits reveals := by
  revert reveals h
  induction commits with
  | nil => intro reveals h; cases reveals <;> simp [checkPairs] at h
  | cons c cs ih =>
      intro reveals h; cases reveals with
      | nil => cases h
      | cons r rs =>
          simp [checkPairs] at h
          split at h <;> try cases h
          · intro hpid; split at h <;> try cases h
            · intro hcom; exact List.Forall2.cons ⟨hpid, hcom⟩ (ih _ h)
            · intro hcom; cases h
          · intro hpid; cases hpid

/-- Checked aggregation is total: always Ok or Error. -/
lemma dkgAggregateChecked_total
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S)) :
  (dkgAggregateChecked S commits reveals).isOk ∨
  (dkgAggregateChecked S commits reveals).isError := by
  cases h : dkgAggregateChecked S commits reveals with
  | ok _ => left; rfl
  | error _ => right; rfl

/-- Ok result → pk equals sum of public shares. -/
lemma dkgAggregateChecked_sound
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (pk : S.Public)
  (h : dkgAggregateChecked S commits reveals = Except.ok pk) :
  pk = (reveals.map (·.pk_i)).sum := by
  unfold dkgAggregateChecked at h
  by_cases hlen : commits.length = reveals.length <;> simp [hlen] at h
  · by_cases hdup : (reveals.map (·.sender)).Nodup <;> simp [hdup] at h
    · simp at h; exact h
    · cases h
  · cases h

/-- Ok result → dkgValid predicate holds. -/
lemma dkgAggregateChecked_ok_valid
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (pk : S.Public)
  (h : dkgAggregateChecked S commits reveals = Except.ok pk) :
  dkgValid S commits reveals := by
  unfold dkgAggregateChecked at h
  by_cases hlen : commits.length = reveals.length <;> simp [hlen] at h
  · by_cases hdup : (reveals.map (·.sender)).Nodup <;> simp [hdup] at h
    ·
      have hpairs : checkPairs S commits reveals = Except.ok () := by
        simp at h; assumption
      have hF := checkPairs_ok_forall2 S commits reveals hpairs
      simpa [dkgValid] using hF
    · cases h
  · cases h

/-!
## Complaint-Based Aggregation

With complaints, Ok result still implies correct pk.
-/

/-- Ok from complaint-based aggregation → correct pk. -/
lemma dkgAggregateWithComplaints_correct
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (pk : S.Public)
  (h : dkgAggregateWithComplaints S commits reveals = Except.ok pk) :
  pk = (reveals.map (·.pk_i)).sum := by
  unfold dkgAggregateWithComplaints at h
  by_cases hlen : commits.length = reveals.length <;> simp [hlen] at h
  · by_cases hcompl : dkgCheckComplaints S commits reveals = [] <;> simp [hcompl] at h
    · simpa using h
    · cases h
  · cases h

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

/-- Binding: same commitment → same public key.
    Uses scheme's commitBinding property. -/
lemma dealer_commit_binding
  (S : Scheme)
  {sh1 sh2 : DealerShare S}
  (h : sh1.commitPk = sh2.commitPk) :
  sh1.pk_i = sh2.pk_i := by
  have hcommit : S.commit sh1.pk_i sh1.opening = S.commit sh2.pk_i sh2.opening := by
    simp only [← DealerShare.commitPk] at h ⊢
    exact h
  exact S.commitBinding hcommit

end IceNine.Security.DKG
