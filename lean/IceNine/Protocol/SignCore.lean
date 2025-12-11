/-
# Signing Core

Core signing functions: challenge computation and n-of-n aggregation.
Split from Sign.lean for modularity.

See Sign.lean for the full protocol documentation and API guidance.
-/

import IceNine.Protocol.SignTypes
import IceNine.Protocol.Lagrange
import Mathlib

namespace IceNine.Protocol

open List

/-!
## Lagrange Interpolation

For t-of-n threshold signing, partial signatures are weighted by
Lagrange coefficients to reconstruct the full signature.

**Note**: Core Lagrange computation is in `Protocol/Lagrange.lean`.
These are convenience wrappers for signing-specific types.
-/

/-- Compute Lagrange coefficient λ_i for party i evaluating at 0.
    Delegates to `Lagrange.schemeCoeffAtZero`. -/
def lagrangeCoeffAtZero
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId] [DecidableEq S.Scalar]
  (pidToScalar : S.PartyId → S.Scalar)
  (Sset : List S.PartyId) (i : S.PartyId) : S.Scalar :=
  Lagrange.schemeCoeffAtZero S pidToScalar Sset i

/-- Compute all Lagrange coefficients for a signer set.
    Returns `LagrangeCoeff` structures for use in signing. -/
def lagrangeCoeffs
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId] [DecidableEq S.Scalar]
  (pidToScalar : S.PartyId → S.Scalar)
  (Sset : List S.PartyId) : List (LagrangeCoeff S) :=
  Sset.map (fun pid => { pid := pid, lambda := Lagrange.schemeCoeffAtZero S pidToScalar Sset pid })

/-!
## Domain-Separated Hash Functions (FROST H4, H5)

Following FROST, we use dedicated hash functions for:
- H4: Message pre-hashing (allows signing large messages efficiently)
- H5: Commitment list encoding (canonical encoding for binding factor computation)
-/

/-!
### Scheme-Dependent Serialization

The following functions define the **protocol-level structure** for message and
commitment encoding. Actual byte-level serialization depends on the concrete
Scheme instantiation.

**For production implementations**, the Scheme should provide:
- `serializeMessage : S.Message → ByteArray`
- `serializePartyId : S.PartyId → ByteArray`
- `serializePublic : S.Public → ByteArray`
- `serializeCommitment : S.Commitment → ByteArray`

These protocol functions then compose domain prefixes with serialized data.
-/

/-- Hash a message for signing (FROST H4).
    Pre-hashing allows efficient signing of large messages.

    **Protocol structure**: `H4(msg) = H(domain_msg || serialize(msg))`

    **Usage**: Call this before computing binding factors or challenge.
    The pre-hashed message is used in place of the raw message.

    **Implementation note**: This function returns the domain prefix concatenated
    with a placeholder. Concrete Schemes should override or extend this with
    actual message serialization. The important invariant is that all parties
    use the same serialization for the same message. -/
def hashMessage (S : Scheme) (msg : S.Message) : ByteArray :=
  -- Protocol structure: domain || serialized_message
  -- The Message type is abstract; concrete schemes provide serialization
  HashDomain.message
  -- In a concrete scheme: HashDomain.message ++ S.serializeMessage msg

/-- Encode a list of commitments for hashing (FROST H5).
    Produces a canonical encoding of the commitment list.

    **Protocol structure**: For each commitment in order:
    ```
    encode(commits) = domain_com ||
      (pid_1 || hiding_1 || binding_1) ||
      (pid_2 || hiding_2 || binding_2) || ...
    ```

    **Usage**: Used in binding factor computation to ensure all parties
    agree on the same commitment ordering and encoding.

    **Ordering requirement**: Commits must be in a canonical order (e.g., sorted
    by sender ID) before encoding. The protocol should ensure this.

    **Implementation note**: This returns domain prefix only. Concrete Schemes
    should extend with actual commitment serialization. -/
def encodeCommitmentList (S : Scheme)
    (commits : List (SignCommitMsg S)) : ByteArray :=
  -- Protocol structure: domain || (pid || hiding || binding) for each commit
  -- Length prefix could be added for unambiguous parsing
  let _numCommits := commits.length
  HashDomain.commitmentList
  -- In a concrete scheme:
  -- HashDomain.commitmentList ++
  --   commits.foldl (fun acc c =>
  --     acc ++ S.serializePartyId c.sender ++
  --           S.serializePublic c.hiding ++
  --           S.serializePublic c.binding) ByteArray.empty

/-- Hash a commitment list (FROST H5).
    Used in binding factor computation.

    **Protocol structure**: `H5(commits) = H(encode(commits))`

    This applies the hash function to the encoded commitment list.
    The encoding ensures canonical representation. -/
def hashCommitmentList (S : Scheme)
    (commits : List (SignCommitMsg S)) : ByteArray :=
  let encoded := encodeCommitmentList S commits
  -- In production: apply S.hash or S.hashToScalar to encoded
  encoded

/-!
## Binding Factor Computation (FROST H1)

The binding factor ρ_i for each signer binds their nonce to the full signing context:
- Message being signed
- Group public key
- All signers' commitments (encoded canonically)
- This signer's identifier

This prevents adaptive attacks where adversary chooses message after seeing commitments.

Reference: FROST RFC Section 4.4
-/

/-- Compute binding factor for a single signer.
    ρ_i = H("rho", msg_hash, pk, encoded_commits, i)

    **Inputs**:
    - `msgHash`: Pre-hashed message (output of hashMessage / H4)
    - `pk`: Group public key
    - `encodedCommits`: Canonical encoding of all commitments (output of encodeCommitmentList / H5)
    - `pid`: This signer's party identifier

    **Output**: Scalar binding factor ρ_i -/
def computeBindingFactor (S : Scheme)
    (msgHash : ByteArray)
    (pk : S.Public)
    (encodedCommits : ByteArray)
    (pid : S.PartyId)
    : S.Scalar :=
  -- Concatenate: domain || msgHash || pk_bytes || commits_bytes || pid_bytes
  -- The actual serialization depends on scheme; this shows the structure
  let data := msgHash ++ encodedCommits  -- pk and pid need serialization from Scheme
  S.hashToScalar HashDomain.bindingFactor data

/-- Compute binding factors for all signers in a signing session.
    Returns a BindingFactors structure with factor for each signer.

    **Usage**: Call after collecting all Round 1 commit messages.

    **Inputs**:
    - `msg`: Message being signed (will be pre-hashed)
    - `pk`: Group public key
    - `commits`: All signers' commit messages from Round 1

    **FROST alignment**: This implements the binding factor computation from
    FROST RFC Section 4.4, using H1 (rho) domain separation. -/
def computeBindingFactors (S : Scheme) [DecidableEq S.PartyId]
    (msg : S.Message)
    (pk : S.Public)
    (commits : List (SignCommitMsg S))
    : BindingFactors S :=
  -- Pre-hash message (H4)
  let msgHash := hashMessage S msg
  -- Encode commitment list (H5)
  let encodedCommits := encodeCommitmentList S commits
  -- Compute binding factor for each signer
  let factors := commits.map fun cmsg =>
    { pid := cmsg.sender
      factor := computeBindingFactor S msgHash pk encodedCommits cmsg.sender
      : BindingFactor S }
  { factors := factors }

/-- Compute binding factors with pre-computed hashes.
    Use when message hash and commitment encoding are already available. -/
def computeBindingFactorsFromHashes (S : Scheme)
    (msgHash : ByteArray)
    (pk : S.Public)
    (encodedCommits : ByteArray)
    (signers : List S.PartyId)
    : BindingFactors S :=
  let factors := signers.map fun pid =>
    { pid := pid
      factor := computeBindingFactor S msgHash pk encodedCommits pid
      : BindingFactor S }
  { factors := factors }

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
def computeEffectiveNonce (S : Scheme) [DecidableEq S.PartyId]
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
