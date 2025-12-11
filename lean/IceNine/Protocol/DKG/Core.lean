/-
# DKG Core

Distributed Key Generation protocol. Parties jointly generate a
shared public key without any party learning the master secret.
Security proofs are in `Proofs/Correctness/DKG`.
-/

import IceNine.Protocol.Core.Core
import Mathlib

namespace IceNine.Protocol

open List

/-!
## Round 1: Commit

Each party samples a secret share sk_i, computes pk_i = A(sk_i),
and broadcasts a commitment to pk_i. The commitment hides pk_i
until all parties have committed, preventing adaptive attacks.

Following FROST, each party also includes a proof of knowledge (PoK)
to prevent rogue-key attacks.
-/

/-- Generate a proof of knowledge for a secret key.
    Proves knowledge of sk such that pk = A(sk).

    Protocol:
    1. Sample random nonce k
    2. Compute R = A(k)
    3. Compute challenge c = H_dkg(pid, pk, R)
    4. Compute response μ = k + c·sk

    **CRITICAL**: The nonce k must be fresh random. Reusing k across
    different proofs leaks the secret key (same as Schnorr nonce reuse). -/
def generateProofOfKnowledge
  (S : Scheme)
  (pid : S.PartyId)       -- prover's identifier
  (sk  : S.Secret)        -- secret key to prove knowledge of
  (pk  : S.Public)        -- public key pk = A(sk)
  (k   : S.Secret)        -- random nonce (MUST be fresh)
  : ProofOfKnowledge S :=
  -- R = A(k)
  let R : S.Public := S.A k
  -- c = H_dkg(pid, pk, R)
  let c : S.Scalar := S.hashDkg pid pk R
  -- μ = k + c·sk
  let μ : S.Secret := k + c • sk
  { commitment := R, response := μ }

/-- Verify a proof of knowledge.
    Checks that the prover knows sk such that pk = A(sk).

    Verification: A(μ) = R + c·pk
    where c = H_dkg(pid, pk, R)

    This works because if μ = k + c·sk, then:
    A(μ) = A(k + c·sk) = A(k) + c·A(sk) = R + c·pk -/
def verifyProofOfKnowledge
  (S : Scheme) [DecidableEq S.Public]
  (pid : S.PartyId)       -- prover's identifier
  (pk  : S.Public)        -- claimed public key
  (pok : ProofOfKnowledge S)
  : Bool :=
  -- c = H_dkg(pid, pk, R)
  let c : S.Scalar := S.hashDkg pid pk pok.commitment
  -- Check: A(μ) = R + c·pk
  let lhs : S.Public := S.A pok.response
  let rhs : S.Public := pok.commitment + c • pk
  lhs = rhs

/-- Proof of knowledge verification as a Prop (for formal proofs). -/
def verifyProofOfKnowledgeProp
  (S : Scheme)
  (pid : S.PartyId)
  (pk  : S.Public)
  (pok : ProofOfKnowledge S)
  : Prop :=
  let c : S.Scalar := S.hashDkg pid pk pok.commitment
  S.A pok.response = pok.commitment + c • pk

/-- Round 1 output: local state (kept private) and commit message (broadcast).
    Party samples sk_i, computes pk_i = A(sk_i), commits to pk_i.
    Also generates proof of knowledge to prevent rogue-key attacks.

    **Inputs**:
    - pid: this party's identifier
    - sk_i: pre-sampled secret share (from CSPRNG)
    - openPk: commitment randomness (from CSPRNG)
    - pokNonce: nonce for proof of knowledge (from CSPRNG, MUST be fresh) -/
def dkgRound1
  (S : Scheme)
  (pid      : S.PartyId)   -- this party's identifier
  (sk_i     : S.Secret)    -- pre-sampled secret share
  (openPk   : S.Opening)   -- commitment randomness
  (pokNonce : S.Secret)    -- nonce for proof of knowledge (MUST be fresh random)
  : DkgLocalState S × DkgCommitMsg S :=
-- Compute public share from secret via one-way map
let pk_i : S.Public := S.A sk_i
-- Commit to public share (hiding it until reveal phase)
let com  : S.Commitment := S.commit pk_i openPk
-- Generate proof of knowledge
let pok : ProofOfKnowledge S := generateProofOfKnowledge S pid sk_i pk_i pokNonce
-- Bundle local state (secret, kept private)
let st   : DkgLocalState S :=
  { pid := pid, sk_i := sk_i, pk_i := pk_i, openPk := openPk }
-- Bundle broadcast message (commitment + PoK)
let msg : DkgCommitMsg S :=
  { sender := pid, commitPk := com, pok := pok }
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
  KeyShare.create S st.pid st.sk_i st.pk_i pk

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
  | invalidProofOfKnowledge : PartyId → DkgError PartyId -- party's PoK failed verification

/-- Verify a single commit message's proof of knowledge.
    Called when commit is received, before reveal phase.
    This is the first line of defense against rogue-key attacks. -/
def verifyCommitPoK
  (S : Scheme) [DecidableEq S.Public]
  (commit : DkgCommitMsg S) (claimedPk : S.Public) :
  Except (DkgError S.PartyId) Unit :=
  if verifyProofOfKnowledge S commit.sender claimedPk commit.pok then
    pure ()
  else throw (.invalidProofOfKnowledge commit.sender)

/-- Verify all commit messages' proofs of knowledge.
    Called after receiving all commits but before reveal phase.

    **Note**: This requires the public keys to be known, which typically
    means we verify during the reveal phase when pk_i becomes available.
    For early verification, implementations may include pk_i in the commit. -/
def verifyAllCommitPoKs
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S))
  (publicKeys : List (S.PartyId × S.Public)) :
  Except (DkgError S.PartyId) Unit :=
  commits.forM fun c =>
    match publicKeys.find? (fun (pid, _) => decide (pid = c.sender)) with
    | some (_, pk) => verifyCommitPoK S c pk
    | none => pure ()  -- pk not yet known, verify later

/-- Check a single commit-reveal pair including PoK verification. -/
def checkPair
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (c : DkgCommitMsg S) (r : DkgRevealMsg S) :
  Except (DkgError S.PartyId) Unit :=
  -- Check party IDs match
  if c.sender = r.sender then
    -- Check commitment opens to revealed value using generic verification
    if verifyCommitmentOpening S r.pk_i r.opening c.commitPk then
      -- Verify proof of knowledge (now that we have pk_i)
      if verifyProofOfKnowledge S c.sender r.pk_i c.pok then
        pure ()
      else throw (.invalidProofOfKnowledge c.sender)
    else throw (.commitMismatch r.sender)
  else throw (.commitMismatch r.sender)

/-- Walk through commit-reveal pairs, checking each opens correctly.
    Requires DecidableEq on all relevant types for runtime checking.
    Terminates because we iterate over the zipped list (structurally decreasing). -/
def checkPairs
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
  (commits : List (DkgCommitMsg S)) (reveals : List (DkgRevealMsg S)) :
  Except (DkgError S.PartyId) Unit :=
  -- First check lengths match
  if commits.length ≠ reveals.length then
    throw .lengthMismatch
  else
    -- Iterate over zipped pairs (terminates: structural recursion on list)
    let pairs := List.zip commits reveals
    pairs.forM (fun (c, r) => checkPair S c r)

/-- Full checked aggregation: validates then computes pk.
    Returns either the global public key or a specific error.

    Validates:
    1. List lengths match
    2. No duplicate party IDs
    3. Each commitment opens correctly
    4. Each proof of knowledge is valid (prevents rogue-key attacks) -/
def dkgAggregateChecked
  (S : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment] [DecidableEq S.Public]
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
  -- Check each commitment opens correctly AND verify PoK
  checkPairs S commits reveals
  -- Compute global public key as sum of shares
  let pk : S.Public := (reveals.map (·.pk_i)).sum
  pure pk

end IceNine.Protocol
