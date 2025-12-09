/-
# Signing (n-of-n) and verification
-/

import IceNine.Protocol.Core
import Mathlib

namespace IceNine.Protocol

open List

/-- Local signing state for one session. -/
structure SignLocalState (S : Scheme) :=
  (share   : KeyShare S)
  (msg     : S.Message)
  (session : Nat)
  (y_i     : S.Secret)
  (w_i     : S.Public)
  (openW   : S.Opening)
deriving Repr

/-- Round-1 signing message: commitment to w_i. -/
structure SignCommitMsg (S : Scheme) :=
  (from    : S.PartyId)
  (session : Nat)
  (commitW : S.Commitment)
deriving Repr

/-- Reveal message for w_i and its opening. -/
structure SignRevealWMsg (S : Scheme) :=
  (from    : S.PartyId)
  (session : Nat)
  (w_i     : S.Public)
  (opening : S.Opening)
deriving Repr

/-- Partial signature share z_i. -/
structure SignShareMsg (S : Scheme) :=
  (from    : S.PartyId)
  (session : Nat)
  (z_i     : S.Secret)
deriving Repr

/-- Lagrange coefficient entry for t-of-n signing. -/
structure LagrangeCoeff (S : Scheme) :=
  (pid : S.PartyId)
  (lambda : S.Scalar)
deriving Repr

/-- Signing errors for non happy-path handling. -/
inductive SignError (PartyId : Type u) where
  | lengthMismatch : SignError PartyId
  | participantMismatch : PartyId → SignError PartyId
  | duplicateParticipants : SignError PartyId
  | commitMismatch : PartyId → SignError PartyId
  | sessionMismatch : Nat → Nat → SignError PartyId
  deriving Repr, DecidableEq

/-- Predicate capturing the consistency checks validated by `validateSigning`. -/
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

/--
  Compute Lagrange coefficient λ_i for evaluation at 0, given participant set Sset
  and an embedding of PartyId into the scalar field.
  Returns 0 if there are duplicate identifiers (which would cause division by 0).
-/
def lagrangeCoeffAtZero
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (pidToScalar : S.PartyId → S.Scalar)
  (Sset : List S.PartyId) (i : S.PartyId) : S.Scalar :=
  let xi := pidToScalar i
  let others := Sset.erase i
  -- If xi coincides with any xj, denominator would be zero; guard by returning 0.
  if hdup : (others.any (fun j => pidToScalar j = xi)) then 0 else
    others.foldl
      (fun acc j =>
        let xj := pidToScalar j
        acc * (xj / (xj - xi)))
      (1 : S.Scalar)

/--
  Compute Lagrange coefficients λ_i for all participants in Sset.
-/
def lagrangeCoeffs
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (pidToScalar : S.PartyId → S.Scalar)
  (Sset : List S.PartyId) : List (LagrangeCoeff S) :=
  Sset.map (fun pid => { pid := pid, lambda := lagrangeCoeffAtZero S pidToScalar Sset pid })

/--
  Signing round 1 (local):
  given a key share and ephemeral randomness y_i + opening for w_i,
  build the local signing state and the commitment message.
-/
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

/--
  Aggregator-side computation of challenge c, given:
  - global pk
  - message m
  - participant set Sset
  - their round-1 commitment messages
  - their w_i reveals.
-/
def computeChallenge
  (S     : Scheme)
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  : Option (S.Challenge × S.Public) :=
  let w : S.Public :=
    reveals.foldl (fun acc r => acc + r.w_i) (0 : S.Public)
  let c : S.Challenge :=
    S.hash m pk Sset (commits.map (fun cmsg => cmsg.commitW)) w
  some (c, w)

/--
  Signing round 2 (local):
  given local signing state and the global challenge c,
  compute a partial signature share z_i.
-/
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

/-- Final threshold signature type. -/
structure Signature (S : Scheme) :=
  (z       : S.Secret)
  (c       : S.Challenge)
  (Sset    : List S.PartyId)
  (commits : List S.Commitment)
deriving Repr

/--
  Aggregate partial shares into a final signature (n-of-n).
-/
def aggregateSignature
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  : Signature S :=
  let z : S.Secret :=
    shares.foldl (fun acc sh => acc + sh.z_i) (0 : S.Secret)
  { z := z, c := c, Sset := Sset, commits := commits }

/--
  Aggregate partial shares into a final signature (t-of-n variant) using
  provided Lagrange coefficients λ_i aligned with the shares list.
-/
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

/--
  Validate a full signing transcript (n-of-n) with basic checks and produce a signature.
  Checks: equal lengths, no duplicate participants, matching pids, commitment openings.
-/
def validateSigning
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  : Except (SignError S.PartyId) (Signature S) := do
  -- length checks
  if hlen : commits.length = reveals.length ∧ reveals.length = shares.length then pure () else
    throw .lengthMismatch
  let sess := (commits.headD (by cases commits <;> simp)).session
  -- participant duplication
  let pids := commits.map (·.from)
  if hdup : pids.Nodup then pure () else throw (.duplicateParticipants (pids.headD (by cases pids <;> simp)))
  -- participant set match
  if hpids : pids = Sset then pure () else throw (.participantMismatch (pids.headD (by cases pids <;> simp)))
  -- commitment openings aligned
  for (c,r) in List.zip commits reveals do
    if hpid : c.from = r.from then
      if hcom : S.commit r.w_i r.opening = c.commitW then
        if hsess : r.session = sess then pure ()
        else throw (.sessionMismatch sess r.session)
      else throw (.commitMismatch r.from)
    else throw (.participantMismatch c.from)
  -- session consistency
  for sh in shares do
    if hsess : sh.session = sess then pure () else throw (.sessionMismatch sess sh.session)
  -- compute c and aggregate
  let w : S.Public := reveals.foldl (fun acc r => acc + r.w_i) (0 : S.Public)
  let c : S.Challenge := S.hash m pk Sset (commits.map (·.commitW)) w
  let sig := aggregateSignature S c Sset (commits.map (·.commitW)) shares
  pure sig

/-- If lengths disagree, validation fails with lengthMismatch. -/
lemma validateSigning_lengthMismatch
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  (h : ¬ (commits.length = reveals.length ∧ reveals.length = shares.length)) :
  validateSigning S pk m Sset commits reveals shares = Except.error (.lengthMismatch) := by
  unfold validateSigning; simp [h]

/-- If duplicate participants, validation fails with duplicateParticipants. -/
lemma validateSigning_duplicate
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  (hlen : commits.length = reveals.length ∧ reveals.length = shares.length)
  (hdup : ¬ (commits.map (·.from)).Nodup) :
  validateSigning S pk m Sset commits reveals shares = Except.error (.duplicateParticipants (commits.headD (by cases commits <;> simp))) := by
  unfold validateSigning; simp [hlen, hdup]

/-- If participant set mismatches, validation fails with participantMismatch. -/
lemma validateSigning_participantMismatch
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  (hlen : commits.length = reveals.length ∧ reveals.length = shares.length)
  (hdup : (commits.map (·.from)).Nodup)
  (hpids : commits.map (·.from) ≠ Sset) :
  validateSigning S pk m Sset commits reveals shares = Except.error (.participantMismatch (commits.headD (by cases commits <;> simp))) := by
  unfold validateSigning; simp [hlen, hdup, hpids]

/-- If any commit opening mismatches, validation fails with commitMismatch. -/
lemma validateSigning_commitMismatch
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  (hlen : commits.length = reveals.length ∧ reveals.length = shares.length)
  (hdup : (commits.map (·.from)).Nodup)
  (hpids : commits.map (·.from) = Sset)
  (hexists : ∃ (c r), (c,r) ∈ List.zip commits reveals ∧ S.commit r.w_i r.opening ≠ c.commitW) :
  ∃ pid, validateSigning S pk m Sset commits reveals shares = Except.error (.commitMismatch pid) := by
  unfold validateSigning
  simp [hlen, hdup, hpids]
  rcases hexists with ⟨c,r,hzr,hm⟩
  -- the first failing pair triggers commitMismatch
  -- we show the for-loop throws; pick its pid
  classical
  -- find index of (c,r)
  have : ∃ pid, True := ⟨r.from, trivial⟩
  exact ⟨r.from, by simp [hm, hzr]⟩

/-- Session/participant uniqueness checks extracted for reuse. -/
def transcriptUnique
  (S : Scheme) [DecidableEq S.PartyId]
  (Sset : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares : List (SignShareMsg S)) : Bool :=
  let pids := commits.map (·.from)
  pids.Nodup ∧ pids = Sset ∧
    let sess := (commits.head?.map (·.session)).getD 0
    (reveals.all (fun r => r.session = sess ∧ r.from ∈ Sset)) ∧
    (shares.all (fun sh => sh.session = sess ∧ sh.from ∈ Sset))

/--
  Adding masks to shares changes aggregated z by the sum of masks.
-/
lemma aggregateSignature_add_masks
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  (mask : S.PartyId → S.Secret) :
  let shares' := shares.map (fun sh => { sh with z_i := sh.z_i + mask sh.from })
  (aggregateSignature S c Sset commits shares').z
    = (aggregateSignature S c Sset commits shares).z
      + (shares.map (fun sh => mask sh.from)).sum := by
  unfold aggregateSignature
  simp [List.map_map, List.foldl_map, add_comm, add_left_comm, add_assoc, List.map, Function.comp]

/--
  If masks sum to zero over shares, aggregateSignature is unchanged.
-/
lemma aggregateSignature_masks_zero
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  (mask : S.PartyId → S.Secret)
  (hzero : (shares.map (fun sh => mask sh.from)).sum = 0) :
  aggregateSignature S c Sset commits (shares.map (fun sh => { sh with z_i := sh.z_i + mask sh.from }))
  = aggregateSignature S c Sset commits shares := by
  ext <;> simp [aggregateSignature_add_masks, hzero, aggregateSignature]

/--
  Verify a threshold signature in the induced single-signer scheme.
-/
def verify
  (S   : Scheme)
  (pk  : S.Public)
  (m   : S.Message)
  (sig : Signature S)
  : Prop :=
  let w' : S.Public := S.A sig.z - (sig.c • pk)
  S.normOK sig.z ∧
    let c' := S.hash m pk sig.Sset sig.commits w'
    c' = sig.c

end IceNine.Protocol
