/-
# DKG Core

Happy-path and checked DKG definitions. Proofs are in `Security/DKG`.
-/

import IceNine.Protocol.Core
import Mathlib

namespace IceNine.Protocol

open List

structure DkgCommitMsg (S : Scheme) :=
  (from    : S.PartyId)
  (commitPk : S.Commitment)
deriving Repr

structure DkgRevealMsg (S : Scheme) :=
  (from    : S.PartyId)
  (pk_i    : S.Public)
  (opening : S.Opening)
deriving Repr

structure DkgLocalState (S : Scheme) :=
  (pid    : S.PartyId)
  (sk_i   : S.Secret)
  (pk_i   : S.Public)
  (openPk : S.Opening)
deriving Repr

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

def dkgRound2
  (S : Scheme)
  (st : DkgLocalState S)
  : DkgRevealMsg S :=
{ from    := st.pid,
  pk_i    := st.pk_i,
  opening := st.openPk }

def dkgValid
  (S : Scheme)
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S)) : Prop :=
  List.Forall2
    (fun c r => c.from = r.from ∧ S.commit r.pk_i r.opening = c.commitPk)
    commits reveals

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

def finalizeKeyShare
  (S : Scheme)
  (st : DkgLocalState S)
  (pk : S.Public)
  : KeyShare S :=
{ pid  := st.pid,
  sk_i := st.sk_i,
  pk_i := st.pk_i,
  pk   := pk }

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

end IceNine.Protocol
