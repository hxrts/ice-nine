/-
# Signing (definitions only)

Two-round threshold signing data structures and core aggregation. Proofs live
in `Security/Sign`.
-/

import IceNine.Protocol.Core
import Mathlib

namespace IceNine.Protocol

open List

structure SignLocalState (S : Scheme) :=
  (share   : KeyShare S)
  (msg     : S.Message)
  (session : Nat)
  (y_i     : S.Secret)
  (w_i     : S.Public)
  (openW   : S.Opening)
deriving Repr

structure SignCommitMsg (S : Scheme) :=
  (from    : S.PartyId)
  (session : Nat)
  (commitW : S.Commitment)
deriving Repr

structure SignRevealWMsg (S : Scheme) :=
  (from    : S.PartyId)
  (session : Nat)
  (w_i     : S.Public)
  (opening : S.Opening)
deriving Repr

structure SignShareMsg (S : Scheme) :=
  (from    : S.PartyId)
  (session : Nat)
  (z_i     : S.Secret)
deriving Repr

structure LagrangeCoeff (S : Scheme) :=
  (pid : S.PartyId)
  (lambda : S.Scalar)
deriving Repr

structure SignError (PartyId : Type u) where
  | lengthMismatch : SignError PartyId
  | participantMismatch : PartyId → SignError PartyId
  | duplicateParticipants : SignError PartyId
  | commitMismatch : PartyId → SignError PartyId
  | sessionMismatch : Nat → Nat → SignError PartyId
  deriving Repr, DecidableEq

structure ValidSignTranscript (S : Scheme)
  (Sset : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S)) : Prop :=
  (len_comm_reveal : commits.length = reveals.length)
  (len_reveal_share : reveals.length = shares.length)
  (pids_nodup : (commits.map (·.from)).Nodup)
  (pids_eq : commits.map (·.from) = Sset)
  (commit_open_ok :
    List.Forall2 (fun c r => c.from = r.from ∧ S.commit r.w_i r.opening = c.commitW) commits reveals)
  (sessions_ok :
    let sess := (commits.head?.map (·.session)).getD 0;
    ∀ sh ∈ shares, sh.session = sess)

def lagrangeCoeffAtZero
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (pidToScalar : S.PartyId → S.Scalar)
  (Sset : List S.PartyId) (i : S.PartyId) : S.Scalar :=
  let xi := pidToScalar i
  let others := Sset.erase i
  if hdup : (others.any (fun j => pidToScalar j = xi)) then 0 else
    others.foldl (fun acc j => let xj := pidToScalar j; acc * (xj / (xj - xi))) (1 : S.Scalar)

def lagrangeCoeffs
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (pidToScalar : S.PartyId → S.Scalar)
  (Sset : List S.PartyId) : List (LagrangeCoeff S) :=
  Sset.map (fun pid => { pid := pid, lambda := lagrangeCoeffAtZero S pidToScalar Sset pid })

def signRound1
  (S : Scheme)
  (ks      : KeyShare S)
  (m       : S.Message)
  (session : Nat)
  (y_i     : S.Secret)
  (openW   : S.Opening)
  : SignLocalState S × SignCommitMsg S :=
let w_i : S.Public := S.A y_i
let com : S.Commitment := S.commit w_i openW
let st  : SignLocalState S :=
  { share   := ks,
    msg     := m,
    session := session,
    y_i     := y_i,
    w_i     := w_i,
    openW   := openW }
let msg1 : SignCommitMsg S :=
  { from    := ks.pid,
    session := session,
    commitW := com }
(st, msg1)

def computeChallenge
  (S     : Scheme)
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  : Option (S.Challenge × S.Public) :=
  let w : S.Public := reveals.foldl (fun acc r => acc + r.w_i) (0 : S.Public)
  let c : S.Challenge := S.hash m pk Sset (commits.map (fun cmsg => cmsg.commitW)) w
  some (c, w)

def signRound2
  (S : Scheme)
  (st : SignLocalState S)
  (c  : S.Challenge)
  : Option (SignShareMsg S) :=
  let z_i : S.Secret := st.y_i + c • st.share.sk_i
  if h : S.normOK z_i then
    some { from    := st.share.pid,
           session := st.session,
           z_i     := z_i }
  else
    none

structure Signature (S : Scheme) :=
  (z       : S.Secret)
  (c       : S.Challenge)
  (Sset    : List S.PartyId)
  (commits : List S.Commitment)
deriving Repr

def aggregateSignature
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  : Signature S :=
  let z : S.Secret := shares.foldl (fun acc sh => acc + sh.z_i) (0 : S.Secret)
  { z := z, c := c, Sset := Sset, commits := commits }

def aggregateSignatureLagrange
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (coeffs : List (LagrangeCoeff S))
  (shares : List (SignShareMsg S))
  : Signature S :=
  let z : S.Secret :=
    List.zipWith (fun coeff sh => coeff.lambda • sh.z_i) coeffs shares
      |>.foldl (fun acc zi => acc + zi) (0 : S.Secret)
  { z := z, c := c, Sset := Sset, commits := commits }

def validateSigning
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  : Except (SignError S.PartyId) (Signature S) := do
  if hlen : commits.length = reveals.length ∧ reveals.length = shares.length then pure () else
    throw .lengthMismatch
  let sess := (commits.headD (by cases commits <;> simp)).session
  let pids := commits.map (·.from)
  if hdup : pids.Nodup then pure () else throw (.duplicateParticipants (pids.headD (by cases pids <;> simp)))
  if hpids : pids = Sset then pure () else throw (.participantMismatch (pids.headD (by cases pids <;> simp)))
  for (c,r) in List.zip commits reveals do
    if hpid : c.from = r.from then
      if hcom : S.commit r.w_i r.opening = c.commitW then
        if hsess : r.session = sess then pure ()
        else throw (.sessionMismatch sess r.session)
      else throw (.commitMismatch r.from)
    else throw (.participantMismatch c.from)
  for sh in shares do
    if hsess : sh.session = sess then pure () else throw (.sessionMismatch sess sh.session)
  let w : S.Public := reveals.foldl (fun acc r => acc + r.w_i) (0 : S.Public)
  let c : S.Challenge := S.hash m pk Sset (commits.map (·.commitW)) w
  let sig := aggregateSignature S c Sset (commits.map (·.commitW)) shares
  pure sig

structure ThresholdCtx (S : Scheme) :=
  (active : Finset S.PartyId)
  (t : Nat)
  (card_ge : t ≤ active.card)

def sharesFromActive (S : Scheme) (ctx : ThresholdCtx S) (shares : List (SignShareMsg S)) : Prop :=
  ∀ sh ∈ shares, sh.from ∈ ctx.active

def aggregateSignatureLagrangeThresh
  (S    : Scheme)
  (c    : S.Challenge)
  (ctx  : ThresholdCtx S)
  (commits : List S.Commitment)
  (coeffs : List (LagrangeCoeff S))
  (shares : List (SignShareMsg S))
  : Signature S :=
  aggregateSignatureLagrange S c ctx.active.toList commits coeffs shares

def coeffsFromCtx
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (ctx : ThresholdCtx S)
  (pidToScalar : S.PartyId → S.Scalar) : List (LagrangeCoeff S) :=
  ctx.active.toList.map (fun pid => { pid := pid, lambda := lagrangeCoeffAtZero S pidToScalar ctx.active.toList pid })

-- Final signature in the CRDT pipeline carries only the signature; context is tracked separately.
structure SignatureDone (S : Scheme) :=
  (sig : Signature S)
deriving Repr

end IceNine.Protocol
