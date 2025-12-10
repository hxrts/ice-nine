/-
# DKG correctness and robustness proofs

Happy-path and checked aggregation lemmas for DKGCore and DKGThreshold, plus
dealer correctness/binding properties.
-/

import IceNine.Protocol.DKGCore
import IceNine.Protocol.DKGThreshold
import IceNine.Protocol.Dealer

namespace IceNine.Security.DKG

open IceNine.Protocol
open List

lemma dkgAggregate_correct
  (S : Scheme)
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (h : dkgValid S commits reveals) :
  dkgAggregate S commits reveals =
    some (reveals.foldl (fun acc r => acc + r.pk_i) (0 : S.Public)) := by
  simp [dkgAggregate, h]

lemma checkPairs_ok_forall2
  (S : Scheme)
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (h : checkPairs S commits reveals = Except.ok ()) :
  List.Forall2 (fun c r => c.from = r.from ∧ S.commit r.pk_i r.opening = c.commitPk) commits reveals := by
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

lemma dkgAggregateChecked_total
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S)) :
  (dkgAggregateChecked S commits reveals).isOk ∨
  (dkgAggregateChecked S commits reveals).isError := by
  by_cases h : dkgAggregateChecked S commits reveals with
  | _ => cases h <;> simp

lemma dkgAggregateChecked_sound
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (pk : S.Public)
  (h : dkgAggregateChecked S commits reveals = Except.ok pk) :
  pk = reveals.foldl (fun acc r => acc + r.pk_i) (0 : S.Public) := by
  unfold dkgAggregateChecked at h
  by_cases hlen : commits.length = reveals.length <;> simp [hlen] at h
  · by_cases hdup : (reveals.map (·.from)).Nodup <;> simp [hdup] at h
    · simp at h; exact h
    · cases h
  · cases h

lemma dkgAggregateChecked_ok_valid
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (pk : S.Public)
  (h : dkgAggregateChecked S commits reveals = Except.ok pk) :
  dkgValid S commits reveals := by
  unfold dkgAggregateChecked at h
  by_cases hlen : commits.length = reveals.length <;> simp [hlen] at h
  · by_cases hdup : (reveals.map (·.from)).Nodup <;> simp [hdup] at h
    ·
      have hpairs : checkPairs S commits reveals = Except.ok () := by
        simp at h; assumption
      have hF := checkPairs_ok_forall2 S commits reveals hpairs
      simpa [dkgValid] using hF
    · cases h
  · cases h

lemma dkgAggregateWithComplaints_correct
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (pk : S.Public)
  (h : dkgAggregateWithComplaints S commits reveals = Except.ok pk) :
  pk = reveals.foldl (fun acc r => acc + r.pk_i) (0 : S.Public) := by
  unfold dkgAggregateWithComplaints at h
  by_cases hlen : commits.length = reveals.length <;> simp [hlen] at h
  · by_cases hcompl : dkgCheckComplaints S commits reveals = [] <;> simp [hcompl] at h
    · simpa using h
    · cases h
  · cases h

lemma dealerKeygen_pk
  (S : Scheme)
  {pids : List S.PartyId} {secrets : List S.Secret} {opens : List S.Opening}
  {tr : DealerTranscript S}
  (h : dealerKeygen S pids secrets opens = some tr) :
  tr.pk = tr.shares.foldl (fun acc sh => acc + sh.pk_i) (0 : S.Public) := by
  unfold dealerKeygen at h
  by_cases hlen : pids.length = secrets.length ∧ secrets.length = opens.length
  · simp [hlen] at h; cases h with | rfl => rfl
  · simp [hlen] at h

lemma dealer_commit_binding
  (S : Scheme)
  {sh1 sh2 : DealerShare S}
  (h : sh1.commitPk = sh2.commitPk) :
  sh1.pk_i = sh2.pk_i := by
  have := S.commitBinding (x₁ := sh1.pk_i) (x₂ := sh2.pk_i) (o₁ := sh1.opening) (o₂ := sh2.opening)
  simpa [DealerShare.commitPk] using this h

end IceNine.Security.DKG
