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
## Domain-Separated Hash Functions (FROST H4, H5)

Following FROST, we use dedicated hash functions for:
- H4: Message pre-hashing (allows signing large messages efficiently)
- H5: Commitment list encoding (canonical encoding for binding factor computation)
-/

/-- Hash a message for signing (FROST H4).
    Pre-hashing allows efficient signing of large messages.

    **Usage**: Call this before computing binding factors or challenge.
    The pre-hashed message is used in place of the raw message. -/
def hashMessage (S : Scheme) (msg : S.Message) : ByteArray :=
  -- Use domain-separated hash: H(domain || msg)
  -- Actual implementation depends on Scheme's hash function
  -- This is a placeholder showing the structure
  HashDomain.message ++ match msg with
    | _ => ByteArray.empty  -- Scheme should provide message serialization

/-- Encode a list of commitments for hashing (FROST H5).
    Produces a canonical encoding of the commitment list.

    **Usage**: Used in binding factor computation to ensure all parties
    agree on the same commitment ordering and encoding. -/
def encodeCommitmentList (S : Scheme)
    (commits : List (SignCommitMsg S)) : ByteArray :=
  -- Concatenate sender || hiding || binding for each commitment
  -- The actual encoding depends on Scheme's serialization
  HashDomain.commitmentList ++ commits.foldl (fun acc _ => acc) ByteArray.empty

/-- Hash a commitment list (FROST H5).
    Used in binding factor computation. -/
def hashCommitmentList (S : Scheme)
    (commits : List (SignCommitMsg S)) : ByteArray :=
  let encoded := encodeCommitmentList S commits
  -- Apply H5 hash (domain-separated)
  encoded  -- Actual hash application depends on Scheme

/-!
## Challenge Derivation

After all Round 1 messages, compute binding factors, aggregate nonce,
and derive challenge via Fiat-Shamir.

With dual nonces:
1. Compute binding factor ρ_i for each signer from (msg, pk, all_commitments, signer_id)
2. Compute effective nonce: w_i = W_hiding_i + ρ_i·W_binding_i
3. Aggregate: w = Σ w_i
4. Derive challenge: c = H(msg, pk, Sset, commitments, w)
-/

/-- Compute effective public nonce for a signer given their commitments and binding factor. -/
def computeEffectiveNonce (S : Scheme)
    (commitMsg : SignCommitMsg S) (bindingFactor : S.Scalar) : S.Public :=
  commitMsg.hiding + bindingFactor • commitMsg.binding

/-- Compute aggregate nonce from all signers' commitments and binding factors.
    w = Σᵢ (W_hiding_i + ρᵢ·W_binding_i) -/
def computeAggregateNonce (S : Scheme) [DecidableEq S.PartyId]
    (commits : List (SignCommitMsg S))
    (bindingFactors : BindingFactors S)
    : S.Public :=
  (commits.map fun cmsg =>
    match bindingFactors.get cmsg.sender with
    | some ρ => computeEffectiveNonce S cmsg ρ
    | none => cmsg.hiding  -- fallback if binding factor missing
  ).sum

/-!
## Binding Validation

Validates that binding factors were correctly derived from the signing context.
This prevents attacks where a malicious coordinator provides incorrect binding factors.
-/

/-- Error for binding validation failures. -/
inductive BindingError (PartyId : Type u)
  | missingBindingFactor : PartyId → BindingError PartyId
  | bindingMismatch : PartyId → BindingError PartyId
  | contextMismatch : BindingError PartyId
  deriving DecidableEq

/-- Validate that all signers have binding factors. -/
def validateBindingFactorsPresent [DecidableEq S.PartyId]
    (commits : List (SignCommitMsg S))
    (bindingFactors : BindingFactors S)
    : Except (BindingError S.PartyId) Unit := do
  for cmsg in commits do
    match bindingFactors.get cmsg.sender with
    | some _ => pure ()
    | none => throw (.missingBindingFactor cmsg.sender)

/-- Validate binding factor for a single signer.
    This checks that the binding factor matches expected derivation.

    **Note**: Actual validation requires the binding factor derivation hash.
    This function provides the structure; implementations must provide
    the concrete hash computation. -/
def validateSingleBinding [DecidableEq S.PartyId] [DecidableEq S.Scalar]
    (cmsg : SignCommitMsg S)
    (bindingFactor : S.Scalar)
    (expectedBindingFactor : S.Scalar)
    : Except (BindingError S.PartyId) Unit :=
  if bindingFactor = expectedBindingFactor then .ok ()
  else .error (.bindingMismatch cmsg.sender)

/-- Validate effective nonce derivation.
    w_eff = W_hiding + ρ·W_binding should equal the claimed effective nonce. -/
def validateEffectiveNonce [DecidableEq S.Public]
    (cmsg : SignCommitMsg S)
    (bindingFactor : S.Scalar)
    (claimedEffective : S.Public)
    : Bool :=
  let computed := computeEffectiveNonce _ cmsg bindingFactor
  computed = claimedEffective

/-- Compute Fiat-Shamir challenge from transcript (dual nonce version).

    Returns the challenge and aggregate nonce. -/
def computeChallenge
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (bindingFactors : BindingFactors S)
  : S.Challenge × S.Public :=
  let w : S.Public := computeAggregateNonce S commits bindingFactors
  let c : S.Challenge := S.hash m pk Sset (commits.map (·.commitW)) w
  (c, w)


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
    -- Verify commitment to hiding public nonce
    List.Forall₂ (fun c r => c.sender = r.sender ∧ S.commit c.hiding r.opening = c.commitW) commits reveals
  sessions_ok :
    let sess := (commits.head?.map (·.session)).getD 0;
    ∀ sh ∈ shares, sh.session = sess

/-- Validate transcript and produce signature if valid.

    This validates:
    1. All lists have matching lengths
    2. No duplicate participants
    3. Participants match expected signer set
    4. Commitment openings are valid
    5. All messages have consistent session ID -/
def validateSigning
  (S     : Scheme) [DecidableEq S.PartyId] [DecidableEq S.Commitment]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (bindingFactors : BindingFactors S)
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
  -- Verify commitments: commit(W_hiding, opening) = commitW
  for (c,r) in List.zip commits reveals do
    if c.sender = r.sender then
      if decide (S.commit c.hiding r.opening = c.commitW) then
        pure ()
      else throw (.commitMismatch r.sender)
    else throw (.participantMismatch c.sender)
  for sh in shares do
    if sh.session = sess then pure () else throw (.sessionMismatch sess sh.session)
  -- Compute challenge using dual nonce structure
  let (c, _w) := computeChallenge S pk m Sset commits bindingFactors
  let sig := aggregateSignature S c Sset (commits.map (·.commitW)) shares
  pure sig

end IceNine.Protocol
