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
  (_h : dkgValid S commits reveals) :
  dkgAggregate S reveals = (reveals.map (·.pk_i)).sum := by
  rfl

/-!
## Soundness Lemmas

Checked aggregation (Ok result) implies the validity predicate.
-/

/-- checkPairs success → Forall₂ validity on pairs.
    Each commit/reveal pair has matching IDs and correct opening.
    TODO: This proof needs work - the checkPairs function has changed. -/
lemma checkPairs_ok_forall2
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (_h : checkPairs S commits reveals = Except.ok ()) :
  List.Forall₂ (fun c r => c.sender = r.sender ∧ S.commit r.pk_i r.opening = c.commitPk) commits reveals := by
  sorry

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
    TODO: Proof needs updating for current dkgAggregateChecked implementation. -/
lemma dkgAggregateChecked_sound
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (pk : S.Public)
  (_h : dkgAggregateChecked S commits reveals = Except.ok pk) :
  pk = (reveals.map (·.pk_i)).sum := by
  sorry

/-- Ok result → dkgValid predicate holds.
    TODO: Proof needs work after checkPairs signature changes. -/
lemma dkgAggregateChecked_ok_valid
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (pk : S.Public)
  (_h : dkgAggregateChecked S commits reveals = Except.ok pk) :
  dkgValid S commits reveals := by
  sorry

/-!
## Complaint-Based Aggregation

With complaints, Ok result still implies correct pk.
-/

/-- Ok from complaint-based aggregation → correct pk.
    TODO: Proof needs work after dkgAggregateWithComplaints signature changes. -/
lemma dkgAggregateWithComplaints_correct
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  [Inhabited S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (pk : S.Public)
  (_h : dkgAggregateWithComplaints S commits reveals = Except.ok pk) :
  pk = (reveals.map (·.pk_i)).sum := by
  sorry

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
    Uses scheme's commitBinding property.
    TODO: Proof needs adjustment for DealerShare structure. -/
lemma dealer_commit_binding
  (S : Scheme)
  {sh1 sh2 : DealerShare S}
  (_h : sh1.commitPk = sh2.commitPk) :
  sh1.pk_i = sh2.pk_i := by
  sorry

end IceNine.Security.DKG
