/-
# Signing Core

Core signing functions: challenge computation and n-of-n aggregation.
Split from Sign.lean for modularity.

See Sign.lean for the full protocol documentation and API guidance.
-/

import IceNine.Protocol.SignTypes
import Mathlib

namespace IceNine.Protocol

open List

/-!
## Lagrange Interpolation

For t-of-n threshold signing, partial signatures are weighted by
Lagrange coefficients to reconstruct the full signature.
-/

/-- Compute Lagrange coefficient λ_i for party i evaluating at 0. -/
def lagrangeCoeffAtZero
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId] [DecidableEq S.Scalar]
  (pidToScalar : S.PartyId → S.Scalar)
  (Sset : List S.PartyId) (i : S.PartyId) : S.Scalar :=
  let xi := pidToScalar i
  let others := Sset.erase i
  if hdup : (others.any (fun j => decide (pidToScalar j = xi))) then 0 else
    (others.map (fun j => let xj := pidToScalar j; xj / (xj - xi))).prod

/-- Compute all Lagrange coefficients for a signer set. -/
def lagrangeCoeffs
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId] [DecidableEq S.Scalar]
  (pidToScalar : S.PartyId → S.Scalar)
  (Sset : List S.PartyId) : List (LagrangeCoeff S) :=
  Sset.map (fun pid => { pid := pid, lambda := lagrangeCoeffAtZero S pidToScalar Sset pid })

/-!
## Challenge Derivation

After all reveals, compute aggregate nonce and derive challenge via Fiat-Shamir.
-/

/-- Compute Fiat-Shamir challenge from transcript. -/
def computeChallenge
  (S     : Scheme)
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  : Option (S.Challenge × S.Public) :=
  let w : S.Public := (reveals.map (·.w_i)).sum
  let c : S.Challenge := S.hash m pk Sset (commits.map (fun cmsg => cmsg.commitW)) w
  some (c, w)

/-!
## Signature Aggregation

Combine partial signatures into final signature.
-/

/-- Simple n-of-n aggregation: z = Σ z_i. -/
def aggregateSignature
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  : Signature S :=
  let z : S.Secret := (shares.map (·.z_i)).sum
  { z := z, c := c, Sset := Sset, commits := commits }

/-- Weighted aggregation: z = Σ λ_i·z_i via provided coefficients. -/
def aggregateSignatureLagrange
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (coeffs : List (LagrangeCoeff S))
  (shares : List (SignShareMsg S))
  : Signature S :=
  let z : S.Secret :=
    (List.zipWith (fun coeff sh => coeff.lambda • sh.z_i) coeffs shares).sum
  { z := z, c := c, Sset := Sset, commits := commits }

/-!
## Transcript Validation

Predicate for valid signing transcripts.
-/

/-- Predicate capturing a valid signing transcript. -/
structure ValidSignTranscript (S : Scheme)
  (Sset : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S)) : Prop where
  len_comm_reveal : commits.length = reveals.length
  len_reveal_share : reveals.length = shares.length
  pids_nodup : (commits.map (·.sender)).Nodup
  pids_eq : commits.map (·.sender) = Sset
  commit_open_ok :
    List.Forall₂ (fun c r => c.sender = r.sender ∧ S.commit r.w_i r.opening = c.commitW) commits reveals
  sessions_ok :
    let sess := (commits.head?.map (·.session)).getD 0;
    ∀ sh ∈ shares, sh.session = sess

/-- Validate transcript and produce signature if valid. -/
def validateSigning
  (S     : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment]
  [Decidable (∀ (r : SignRevealWMsg S) (c : SignCommitMsg S), S.commit r.w_i r.opening = c.commitW)]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  : Except (SignError S.PartyId) (Signature S) := do
  if commits.length = reveals.length ∧ reveals.length = shares.length then pure () else
    throw .lengthMismatch
  let sess := (commits.head?.map (·.session)).getD 0
  let pids := commits.map (·.sender)
  if pids.Nodup then pure () else
    let firstPid := pids.head!
    throw (.duplicateParticipants firstPid)
  if pids = Sset then pure () else
    let mismatch := pids.find? (· ∉ Sset) |>.orElse (fun _ => Sset.find? (· ∉ pids))
    match mismatch with
    | some pid => throw (.participantMismatch pid)
    | none => throw .lengthMismatch
  for (c,r) in List.zip commits reveals do
    if c.sender = r.sender then
      if decide (S.commit r.w_i r.opening = c.commitW) then
        if r.session = sess then pure ()
        else throw (.sessionMismatch sess r.session)
      else throw (.commitMismatch r.sender)
    else throw (.participantMismatch c.sender)
  for sh in shares do
    if sh.session = sess then pure () else throw (.sessionMismatch sess sh.session)
  let w : S.Public := (reveals.map (·.w_i)).sum
  let c : S.Challenge := S.hash m pk Sset (commits.map (·.commitW)) w
  let sig := aggregateSignature S c Sset (commits.map (·.commitW)) shares
  pure sig

end IceNine.Protocol
