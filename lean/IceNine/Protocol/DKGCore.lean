/-
# DKG Core (shared types and n-of-n happy path)
-/

import IceNine.Protocol.Core
import Mathlib

namespace IceNine.Protocol

open List

/-- DKG round-1 message: commitment to pk_i. -/
structure DkgCommitMsg (S : Scheme) :=
  (from    : S.PartyId)
  (commitPk : S.Commitment)
deriving Repr

/-- DKG round-2 message: reveal pk_i and opening. -/
structure DkgRevealMsg (S : Scheme) :=
  (from    : S.PartyId)
  (pk_i    : S.Public)
  (opening : S.Opening)
deriving Repr

/-- Local state for DKG after round 1. -/
structure DkgLocalState (S : Scheme) :=
  (pid    : S.PartyId)
  (sk_i   : S.Secret)
  (pk_i   : S.Public)
  (openPk : S.Opening)
deriving Repr

/--
  Local DKG round 1: sample sk_i, compute pk_i = A sk_i,
  and produce a commitment message.
-/
def dkgRound1
  (S : Scheme)
  (pid     : S.PartyId)
  (sk_i    : S.Secret)
  (openPk  : S.Opening)
  : DkgLocalState S × DkgCommitMsg S :=
let pk_i : S.Public := S.A sk_i
let com  : S.Commitment := S.commit pk_i openPk
let st   : DkgLocalState S :=
  { pid := pid, sk_i := sk_i, pk_i := pk_i, openPk := openPk }
let msg : DkgCommitMsg S :=
  { from := pid, commitPk := com }
(st, msg)

/-- Local DKG round 2: reveal pk_i with opening. -/
def dkgRound2
  (S : Scheme)
  (st : DkgLocalState S)
  : DkgRevealMsg S :=
{ from    := st.pid,
  pk_i    := st.pk_i,
  opening := st.openPk }

/-- Commit/reveal consistency for DKG. -/
def dkgValid
  (S : Scheme)
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S)) : Prop :=
  List.Forall2
    (fun c r => c.from = r.from ∧ S.commit r.pk_i r.opening = c.commitPk)
    commits reveals

/--
  Aggregate DKG: verify commitments against reveals and compute pk = Σ pk_i.
  Returns `none` on mismatched length or failed checks.
-/
def dkgAggregate
  (S : Scheme)
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  : Option S.Public :=
  match h : dkgValid S commits reveals with
  | False => none
  | True =>
      let pk : S.Public :=
        reveals.foldl (fun acc r => acc + r.pk_i) (0 : S.Public)
      some pk

/--
  If `dkgValid` holds, aggregation succeeds with the sum of revealed pk_i.
-/
lemma dkgAggregate_correct
  (S : Scheme)
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (h : dkgValid S commits reveals) :
  dkgAggregate S commits reveals =
    some (reveals.foldl (fun acc r => acc + r.pk_i) (0 : S.Public)) := by
  simp [dkgAggregate, h]

/--
  Finalize local key share once the global pk is known.
-/
def finalizeKeyShare
  (S : Scheme)
  (st : DkgLocalState S)
  (pk : S.Public)
  : KeyShare S :=
{ pid  := st.pid,
  sk_i := st.sk_i,
  pk_i := st.pk_i,
  pk   := pk }

/-- Possible DKG errors (non happy-path). -/
inductive DkgError (PartyId : Type u) where
  | lengthMismatch : DkgError PartyId
  | duplicatePids  : DkgError PartyId
  | commitMismatch : PartyId → DkgError PartyId
  deriving Repr, DecidableEq

partial def checkPairs
  (S : Scheme) (commits : List (DkgCommitMsg S)) (reveals : List (DkgRevealMsg S)) :
  Except (DkgError S.PartyId) Unit :=
  match commits, reveals with
  | [], [] => pure ()
  | c::cs, r::rs =>
      if hpid : c.from = r.from then
        if hcom : S.commit r.pk_i r.opening = c.commitPk then
          checkPairs S cs rs
        else throw (.commitMismatch r.from)
      else throw (.commitMismatch r.from)
  | _, _ => throw (.lengthMismatch)

lemma checkPairs_ok_forall2
  (S : Scheme)
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  (h : checkPairs S commits reveals = Except.ok ()) :
  List.Forall2 (fun c r => c.from = r.from ∧ S.commit r.pk_i r.opening = c.commitPk) commits reveals := by
  revert reveals h
  induction commits with
  | nil =>
      intro reveals h
      cases reveals <;> simp [checkPairs] at h
      · simp
      · cases h
  | cons c cs ih =>
      intro reveals h
      cases reveals with
      | nil => cases h
      | cons r rs =>
          simp [checkPairs] at h
          split at h <;> try cases h
          · intro hpid
            split at h <;> try cases h
            · intro hcom
              specialize ih _ h
              exact List.Forall2.cons ⟨hpid, hcom⟩ ih
            · intro hcom; cases hcom
          · intro hpid; cases hpid

/--
  Robust DKG aggregation with simple error reporting.
  Checks length equality, duplicate pids, and commitment consistency.
-/
def dkgAggregateChecked
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  : Except (DkgError S.PartyId) S.Public := do
  if hlen : commits.length = reveals.length then pure () else
    throw (.lengthMismatch)
  let pids := reveals.map (·.from)
  if hdup : pids.Nodup then pure () else
    throw (.duplicatePids)
  checkPairs S commits reveals
  let pk : S.Public := reveals.foldl (fun acc r => acc + r.pk_i) (0 : S.Public)
  pure pk

/-- Totality: checked aggregation either succeeds or returns an error. -/
lemma dkgAggregateChecked_total
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S)) :
  (dkgAggregateChecked S commits reveals).isOk ∨
  (dkgAggregateChecked S commits reveals).isError := by
  by_cases h : dkgAggregateChecked S commits reveals with
  | _ => cases h <;> simp

/--
  If `dkgAggregateChecked` succeeds, it matches the simple fold of pk_i.
-/
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
    ·
      simp at h
      exact h
    · cases h
  · cases h

/-- If aggregation succeeds, then dkgValid holds (all pairs match). -/
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
        simp at h
        assumption
      have hF := checkPairs_ok_forall2 S commits reveals hpairs
      simpa [dkgValid] using hF
    · cases h
  · cases h

end IceNine.Protocol
