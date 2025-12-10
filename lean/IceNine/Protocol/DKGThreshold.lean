/-
# Threshold DKG

Complaint-based DKG aggregation for t-of-n. Proofs live in `Security/DKG`.
-/

import IceNine.Protocol.DKGCore
import Mathlib

namespace IceNine.Protocol

open List

inductive Complaint (PartyId : Type u) where
  | openingMismatch (accused : PartyId)
  | missingReveal (accused : PartyId)
  deriving Repr, DecidableEq

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

end IceNine.Protocol
