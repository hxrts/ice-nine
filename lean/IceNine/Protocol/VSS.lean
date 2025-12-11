/-
# Verifiable Secret Sharing Protocol

VSS-enhanced DKG protocol providing malicious security. Each party acts as
a dealer for their own secret share, committing to a polynomial and proving
their shares are consistent.

This provides:
- **Verifiability**: Recipients can verify shares are on committed polynomial
- **Malicious security**: Cheating dealers are detected before shares are used
- **Complaint mechanism**: Invalid shares generate verifiable complaints

**Reference**: Pedersen, "Non-Interactive and Information-Theoretic Secure
Verifiable Secret Sharing", CRYPTO 1991.
-/

import IceNine.Protocol.VSSCore
import IceNine.Protocol.DKGThreshold
import Mathlib

namespace IceNine.Protocol.VSS

open IceNine.Protocol

/-!
## VSS-DKG Message Types

In VSS-DKG, each party i:
1. Samples polynomial f_i(x) with f_i(0) = sk_i (their secret share contribution)
2. Broadcasts commitment to f_i
3. Sends share f_i(j) privately to each party j
4. Receives shares from all other parties and verifies them
-/

/-- VSS commitment message: party broadcasts their polynomial commitment. -/
structure VSSCommitMsg (S : Scheme) where
  sender : S.PartyId
  /-- Commitment to polynomial coefficients -/
  polyCommit : PolyCommitment S

/-- VSS share message: party sends share privately to recipient. -/
structure VSSShareMsg (S : Scheme) where
  sender : S.PartyId
  recipient : S.PartyId
  /-- The share value f_sender(recipient) -/
  share : VSSShare S

/-- VSS complaint: party j complains that party i's share is invalid. -/
structure VSSComplaint (S : Scheme) where
  /-- Party filing the complaint -/
  complainant : S.PartyId
  /-- Party being accused -/
  accused : S.PartyId
  /-- The share that failed verification (for public verification) -/
  badShare : VSSShare S
  /-- The commitment it should verify against -/
  commitment : PolyCommitment S

/-- VSS error types. -/
inductive VSSError (PartyId : Type*) where
  | shareVerificationFailed : PartyId → PartyId → VSSError PartyId  -- (accused, complainant)
  | missingCommitment : PartyId → VSSError PartyId
  | missingShare : PartyId → PartyId → VSSError PartyId  -- (from, to)
  | thresholdMismatch : Nat → Nat → VSSError PartyId  -- (expected, got)
  | duplicateDealer : PartyId → VSSError PartyId
deriving DecidableEq, Repr

/-!
## Party State for VSS-DKG

Each party maintains:
- Their own polynomial and commitment
- Shares received from other parties
- Verification results
-/

/-- Party's local state during VSS-DKG. -/
structure VSSLocalState (S : Scheme) where
  /-- This party's ID -/
  pid : S.PartyId
  /-- This party's polynomial (secret) -/
  polynomial : Polynomial S.Secret
  /-- This party's commitment (public) -/
  commitment : PolyCommitment S
  /-- Shares this party has generated for others -/
  outgoingShares : List (VSSShareMsg S)
  /-- Shares received from other parties -/
  incomingShares : List (VSSShareMsg S)
  /-- Complaints filed by this party -/
  complaints : List (VSSComplaint S)

/-!
## VSS-DKG Protocol Functions
-/

/-- Initialize VSS state for a party.
    Party samples polynomial with their secret contribution as constant term. -/
def vssInit (S : Scheme) [Semiring S.Secret] [Monoid S.Scalar] [Module S.Scalar S.Secret]
    (pid : S.PartyId)
    (secretContribution : S.Secret)  -- sk_i: this party's share of the master secret
    (randomCoeffs : List S.Secret)   -- random coefficients for polynomial
    (parties : List (S.PartyId × S.Scalar))  -- all parties with their eval points
    : VSSLocalState S :=
  let poly := mkPolynomial secretContribution randomCoeffs
  let commit := commitPolynomial S poly
  let shares := parties.map fun (recipient, evalPt) =>
    { sender := pid
      recipient := recipient
      share := generateShare S poly recipient evalPt }
  { pid := pid
    polynomial := poly
    commitment := commit
    outgoingShares := shares
    incomingShares := []
    complaints := [] }

/-- Generate commit message for broadcast. -/
def vssCommitMsg (S : Scheme) (st : VSSLocalState S) : VSSCommitMsg S :=
  { sender := st.pid
    polyCommit := st.commitment }

/-- Get share message for a specific recipient. -/
def vssShareMsgFor (S : Scheme) [DecidableEq S.PartyId]
    (st : VSSLocalState S) (recipient : S.PartyId) : Option (VSSShareMsg S) :=
  st.outgoingShares.find? (fun m => m.recipient = recipient)

/-- Receive and verify a share from another party.
    Returns updated state with share added (if valid) or complaint filed. -/
def vssReceiveShare (S : Scheme) [Module S.Scalar S.Public] [DecidableEq S.Public]
    (st : VSSLocalState S)
    (msg : VSSShareMsg S)
    (senderCommit : PolyCommitment S)
    : VSSLocalState S :=
  -- Verify the share against sender's commitment
  if verifyShareBool S senderCommit msg.share then
    -- Valid: add to incoming shares
    { st with incomingShares := msg :: st.incomingShares }
  else
    -- Invalid: file complaint
    let complaint : VSSComplaint S :=
      { complainant := st.pid
        accused := msg.sender
        badShare := msg.share
        commitment := senderCommit }
    { st with
      incomingShares := msg :: st.incomingShares  -- keep for record
      complaints := complaint :: st.complaints }

/-- Verify a complaint is valid (the share really doesn't verify). -/
def verifyComplaint (S : Scheme) [Module S.Scalar S.Public] [DecidableEq S.Public]
    (complaint : VSSComplaint S) : Bool :=
  -- Complaint is valid if the share does NOT verify
  !verifyShareBool S complaint.commitment complaint.badShare

/-!
## Share Aggregation

After VSS completes, each party j holds:
- Shares s_{i,j} = f_i(j) from each honest dealer i
- Their aggregate share: sk_j = Σ_i s_{i,j}

The global secret is sk = Σ_i sk_i = Σ_i f_i(0)
-/

/-- Aggregate received shares to compute party's final secret share.
    sk_j = Σ_i s_{i,j} where s_{i,j} is share from party i to party j. -/
def aggregateReceivedShares (S : Scheme)
    (incomingShares : List (VSSShareMsg S)) : S.Secret :=
  (incomingShares.map (·.share.value)).sum

/-- Compute party's public share from aggregated secret share.
    pk_j = A(sk_j) -/
def computePublicShare (S : Scheme) (sk_j : S.Secret) : S.Public :=
  S.A sk_j

/-- Finalize VSS-DKG for a party: compute their KeyShare. -/
def vssFinalize (S : Scheme)
    (st : VSSLocalState S)
    (allCommitments : List (VSSCommitMsg S))
    : Option (KeyShare S) :=
  -- Check no complaints
  if st.complaints.isEmpty then
    -- Aggregate secret share
    let sk_i := aggregateReceivedShares S st.incomingShares
    -- Compute public share
    let pk_i := computePublicShare S sk_i
    -- Compute global public key from commitments
    -- pk = Σ_i A(a_{i,0}) = Σ_i C_{i,0} (first commitment from each dealer)
    let pk := (allCommitments.filterMap (fun c => c.polyCommit.commitments.head?)).sum
    some { pid := st.pid
           secret := SecretBox.mk sk_i
           pk_i := pk_i
           pk := pk }
  else
    -- Has complaints: VSS failed
    none

/-!
## VSS-DKG Transcript

Complete transcript for verification and blame attribution.
-/

/-- Complete VSS-DKG transcript. -/
structure VSSDKGTranscript (S : Scheme) where
  /-- All commitment messages -/
  commitments : List (VSSCommitMsg S)
  /-- All share messages (normally private, revealed for disputes) -/
  shares : List (VSSShareMsg S)
  /-- All complaints filed -/
  complaints : List (VSSComplaint S)
  /-- Threshold (degree + 1) -/
  threshold : Nat

/-- Check if VSS-DKG succeeded (no valid complaints). -/
def vssDKGSuccess (S : Scheme) [Module S.Scalar S.Public] [DecidableEq S.Public]
    (transcript : VSSDKGTranscript S) : Bool :=
  -- Success if all complaints are invalid (shares actually verify)
  transcript.complaints.all (fun c => !verifyComplaint S c)

/-- Get list of faulty parties (those with valid complaints against them). -/
def vssFaultyParties (S : Scheme) [Module S.Scalar S.Public] [DecidableEq S.Public]
    [DecidableEq S.PartyId]
    (transcript : VSSDKGTranscript S) : List S.PartyId :=
  (transcript.complaints.filter (fun c => verifyComplaint S c)).map (·.accused)
  |>.dedup

end IceNine.Protocol.VSS
