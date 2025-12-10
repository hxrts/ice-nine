/-
# DKG Core

Distributed Key Generation protocol. Parties jointly generate a
shared public key without any party learning the master secret.
Security proofs are in `Security/DKG`.
-/

import IceNine.Protocol.Core
import Mathlib

namespace IceNine.Protocol

open List

/-!
## Round 1: Commit

Each party samples a secret share sk_i, computes pk_i = A(sk_i),
and broadcasts a commitment to pk_i. The commitment hides pk_i
until all parties have committed, preventing adaptive attacks.
-/

/-- Round 1 output: local state (kept private) and commit message (broadcast).
    Party samples sk_i, computes pk_i = A(sk_i), commits to pk_i. -/
def dkgRound1
  (S : Scheme)
  (pid     : S.PartyId)   -- this party's identifier
  (sk_i    : S.Secret)    -- pre-sampled secret share
  (openPk  : S.Opening)   -- commitment randomness
  : DkgLocalState S × DkgCommitMsg S :=
-- Compute public share from secret via one-way map
let pk_i : S.Public := S.A sk_i
-- Commit to public share (hiding it until reveal phase)
let com  : S.Commitment := S.commit pk_i openPk
-- Bundle local state (secret, kept private)
let st   : DkgLocalState S :=
  { pid := pid, sk_i := sk_i, pk_i := pk_i, openPk := openPk }
-- Bundle broadcast message (commitment only)
let msg : DkgCommitMsg S :=
  { sender := pid, commitPk := com }
(st, msg)

/-!
## Round 2: Reveal

After receiving all commitments, each party reveals its pk_i and
the opening. Others verify: commit(pk_i, opening) = received commitment.
-/

/-- Round 2: reveal pk_i and opening so others can verify commitment. -/
def dkgRound2
  (S : Scheme)
  (st : DkgLocalState S)
  : DkgRevealMsg S :=
{ sender  := st.pid,
  pk_i    := st.pk_i,
  opening := st.openPk }

/-!
## Validation and Aggregation

After collecting all reveals, verify each commitment opens correctly,
then sum the public shares to get the global public key: pk = Σ pk_i.
-/

/-- Validity predicate: each reveal matches its commitment.
    Forall₂ ensures lists are same length and pairwise valid. -/
def dkgValid
  (S : Scheme)
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S)) : Prop :=
  List.Forall₂
    (fun c r => c.sender = r.sender ∧ S.commit r.pk_i r.opening = c.commitPk)
    commits reveals

/-- Simple aggregation: returns pk always (validation done separately).
    pk = Σ pk_i is the global public key for signing. -/
def dkgAggregate
  (S : Scheme)
  (reveals : List (DkgRevealMsg S))
  : S.Public :=
  -- Sum all public shares to get global public key
  (reveals.map (·.pk_i)).sum

/-- Convert DKG local state to a KeyShare once pk is known.
    This is the credential a party carries into signing. -/
def finalizeKeyShare
  (S : Scheme)
  (st : DkgLocalState S)
  (pk : S.Public)         -- global pk from aggregation
  : KeyShare S :=
{ pid  := st.pid,
  sk_i := st.sk_i,
  pk_i := st.pk_i,
  pk   := pk }

/-!
## Error Handling

Structured errors identify exactly what went wrong during DKG.
Enables blame attribution and recovery strategies.
-/

/-- DKG failure modes with identifying information. -/
inductive DkgError (PartyId : Type*) where
  | lengthMismatch : DkgError PartyId           -- commits/reveals count differs
  | duplicatePids  : DkgError PartyId           -- same party appears twice
  | commitMismatch : PartyId → DkgError PartyId -- party's reveal doesn't match commit

/-- Walk through commit-reveal pairs, checking each opens correctly.
    Requires DecidableEq on all relevant types for runtime checking. -/
partial def checkPairs
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment]
  (commits : List (DkgCommitMsg S)) (reveals : List (DkgRevealMsg S)) :
  Except (DkgError S.PartyId) Unit :=
  match commits, reveals with
  | [], [] => pure ()
  | c::cs, r::rs =>
      -- Check party IDs match
      if c.sender = r.sender then
        -- Check commitment opens to revealed value
        if S.commit r.pk_i r.opening = c.commitPk then
          checkPairs S cs rs
        else throw (.commitMismatch r.sender)
      else throw (.commitMismatch r.sender)
  | _, _ => throw (.lengthMismatch)

/-- Full checked aggregation: validates then computes pk.
    Returns either the global public key or a specific error. -/
def dkgAggregateChecked
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  : Except (DkgError S.PartyId) S.Public := do
  -- Check list lengths match
  if hlen : commits.length = reveals.length then pure () else
    throw (.lengthMismatch)
  -- Check no duplicate party IDs
  let pids := reveals.map (·.sender)
  if hdup : pids.Nodup then pure () else
    throw (.duplicatePids)
  -- Check each commitment opens correctly
  checkPairs S commits reveals
  -- Compute global public key as sum of shares
  let pk : S.Public := (reveals.map (·.pk_i)).sum
  pure pk

end IceNine.Protocol
