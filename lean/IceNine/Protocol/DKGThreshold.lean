/-
# Threshold DKG (t-of-n) with complaints (lattice, additive shares)
-/

import IceNine.Protocol.DKGCore
import IceNine.Protocol.Sign
import Mathlib

namespace IceNine.Protocol

open List

/-- Complaint reasons during DKG. -/
inductive Complaint (PartyId : Type u) where
  | openingMismatch (accused : PartyId)
  | missingReveal (accused : PartyId)
  deriving Repr, DecidableEq

/--
  Verify reveals against commits; return list of complaints (empty = happy path).
-/
def dkgCheckComplaints
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  : List (Complaint S.PartyId) :=
  let pairs := List.zip commits reveals
  pairs.foldl
    (fun acc (c,r) =>
      if hpid : c.from = r.from then
        if hcom : S.commit r.pk_i r.opening = c.commitPk then acc
        else Complaint.openingMismatch r.from :: acc
      else Complaint.openingMismatch r.from :: acc)
    []

/--
  Attempt aggregation with complaints; returns pk on success, or list of complaints.
-/
def dkgAggregateWithComplaints
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  : Except (List (Complaint S.PartyId)) S.Public :=
  if hlen : commits.length = reveals.length then
    let cs := dkgCheckComplaints S commits reveals
    if hnil : cs = [] then
      let pk := reveals.foldl (fun acc r => acc + r.pk_i) (0 : S.Public)
      Except.ok pk
    else
      Except.error cs
  else
    Except.error [Complaint.missingReveal (commits.head?.map (·.from)).getD (reveals.head?.map (·.from)).getD (default)]

/--
  Correctness: if no complaints are returned, pk equals the sum of pk_i.
-/
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

end IceNine.Protocol
