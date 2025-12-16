/-
# DKG-Based Share Refresh

Distributed share refresh without a trusted coordinator.
Each party generates a zero-polynomial and distributes shares.
The sum of all zero-shares updates each party's share while
preserving the master secret.

## Comparison: RefreshDKG vs RefreshCoord

| Aspect | RefreshDKG (this module) | RefreshCoord |
|--------|--------------------------|--------------|
| **Trust model** | Fully distributed, no coordinator | Single coordinator computes adjustment |
| **Communication** | O(n²) messages (each party sends to all) | O(n) messages (all to/from coordinator) |
| **Rounds** | 3 rounds (commit, share, aggregate) | 4 phases (commit, reveal, adjust, apply) |
| **Verifiability** | Each share verifiable against commitment | Relies on coordinator honesty |
| **Fault tolerance** | Can identify malicious parties | Coordinator is single point of failure |
| **Use case** | High security, trustless environments | Lower latency, trusted coordinator available |

**When to use RefreshDKG**:
- No party should learn all refresh masks
- Need to identify malicious parties during refresh
- Participants don't trust each other

**When to use RefreshCoord**:
- A trusted coordinator exists (e.g., the dealer)
- Lower communication overhead is important
- Simpler integration with existing coordinator infrastructure

## Protocol Overview

1. **Round 1 (Commit)**: Each party generates a random polynomial with constant term 0,
   commits to the polynomial coefficients.

2. **Round 2 (Share)**: Each party sends evaluation of their polynomial to other parties.

3. **Round 3 (Aggregate)**: Each party verifies received shares against commitments,
   sums all shares to get their refresh delta.

## Security Properties

- **Zero-sum**: Sum of all deltas is zero (master secret unchanged)
- **Unlinkability**: Old and new shares are unlinkable without threshold cooperation
- **Verifiable**: Each share can be verified against polynomial commitment

Reference: FROST RFC Section 7.1, Proactive Secret Sharing (Herzberg et al. 1995)
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.DKG.Feldman
import Mathlib

namespace IceNine.Protocol.RefreshDKG

open IceNine.Protocol

/-!
## Round 1: Zero-Polynomial Commitment

Each party generates a polynomial f_i(x) with f_i(0) = 0 (zero constant term).
This ensures the sum of all polynomials at x=0 is zero.
-/

/-- Local state for refresh DKG participant. -/
structure RefreshLocalState (S : Scheme) where
  /-- This party's identifier -/
  pid : S.PartyId
  /-- Zero-polynomial coefficients [0, a₁, a₂, ..., a_{t-1}] -/
  coefficients : List S.Secret
  /-- Opening for polynomial commitment -/
  opening : S.Opening

/-- Round 1 commit message: commitment to zero-polynomial. -/
structure RefreshCommitMsg (S : Scheme) [CommRing S.Scalar] where
  sender : S.PartyId
  /-- Polynomial commitment (public coefficients) -/
  polyCommit : VSS.PolyCommitment S

/-- Round 2 share message: evaluation of zero-polynomial for recipient. -/
structure RefreshShareMsg (S : Scheme) where
  sender : S.PartyId
  recipient : S.PartyId
  /-- f_sender(recipient) - the share value -/
  share : S.Secret

/-- Round 3 result: the refresh delta for this party. -/
structure RefreshDelta (S : Scheme) where
  pid : S.PartyId
  /-- Sum of all received shares: δ_i = Σⱼ f_j(i) -/
  delta : S.Secret

/-!
## Round 1: Generate Zero-Polynomial and Commit
-/

/-- Generate a zero-polynomial of degree t-1.
    The polynomial has form: f(x) = a₁x + a₂x² + ... + a_{t-1}x^{t-1}
    Note: constant term is 0, ensuring f(0) = 0. -/
def generateZeroPolynomial
    (S : Scheme)
    (randomCoeffs : List S.Secret)  -- [a₁, a₂, ..., a_{t-1}]
    : List S.Secret :=
  -- Prepend zero as constant term
  0 :: randomCoeffs

/-- Round 1: Generate commitment to zero-polynomial.
    Returns local state (kept private) and commit message (broadcast). -/
noncomputable def refreshRound1
    (S : Scheme) [CommRing S.Scalar]
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [AddCommGroup S.Public] [Module S.Scalar S.Public]
    (pid : S.PartyId)
    (randomCoeffs : List S.Secret)  -- random coefficients a₁...a_{t-1}
    (opening : S.Opening)
    : RefreshLocalState S × RefreshCommitMsg S :=
  let coeffs := generateZeroPolynomial S randomCoeffs
  let polyCommit := VSS.commitPolynomialFromCoeffs S coeffs
  let st : RefreshLocalState S := {
    pid := pid
    coefficients := coeffs
    opening := opening
  }
  let msg : RefreshCommitMsg S := {
    sender := pid
    polyCommit := polyCommit
  }
  (st, msg)

/-!
## Round 2: Distribute Shares
-/

/-- Evaluate polynomial at a point using Horner's method.
    f(x) = a₀ + a₁x + a₂x² + ... = a₀ + x(a₁ + x(a₂ + ...)) -/
def evalPolynomial
    (S : Scheme) [Mul S.Scalar] [Add S.Secret]
    (pidToScalar : S.PartyId → S.Scalar)
    (coeffs : List S.Secret)
    (evalPoint : S.PartyId)
    : S.Secret :=
  let x := pidToScalar evalPoint
  -- Horner's method: fold from highest degree
  coeffs.reverse.foldl (fun acc c => c + x • acc) 0

/-- Round 2: Generate shares for all other parties.
    Each party evaluates their polynomial at each other party's point. -/
def refreshRound2
    (S : Scheme) [Mul S.Scalar] [Add S.Secret] [DecidableEq S.PartyId]
    (pidToScalar : S.PartyId → S.Scalar)
    (st : RefreshLocalState S)
    (allParties : List S.PartyId)
    : List (RefreshShareMsg S) :=
  allParties.filterMap fun recipient =>
    if recipient = st.pid then none  -- don't send to self
    else some {
      sender := st.pid
      recipient := recipient
      share := evalPolynomial S pidToScalar st.coefficients recipient
    }

/-- Compute own share (self-evaluation). -/
def computeOwnShare
    (S : Scheme) [Mul S.Scalar] [Add S.Secret]
    (pidToScalar : S.PartyId → S.Scalar)
    (st : RefreshLocalState S)
    : S.Secret :=
  evalPolynomial S pidToScalar st.coefficients st.pid

/-!
## Round 3: Verify and Aggregate
-/

/-- Verify a received share against the sender's polynomial commitment.
    Checks: A(share) = expectedPublicValue(polyCommit, recipient)

    The expected public value is computed by evaluating the commitment
    polynomial at the recipient's point. -/
noncomputable def verifyRefreshShare
    (S : Scheme) [CommRing S.Scalar] [DecidableEq S.PartyId] [DecidableEq S.Public]
    [AddCommGroup S.Public] [Module S.Scalar S.Public]
    (pidToScalar : S.PartyId → S.Scalar)
    (commits : List (RefreshCommitMsg S))
    (shareMsg : RefreshShareMsg S)
    : Bool :=
  match commits.find? (fun c => c.sender == shareMsg.sender) with
  | none => false  -- no commitment from this sender
  | some commitMsg =>
      -- Compute expected public value at recipient's point
      let x := pidToScalar shareMsg.recipient
      let expectedPub := VSS.expectedPublicValue S commitMsg.polyCommit x
      -- Verify A(share) = expected
      S.A shareMsg.share = expectedPub

/-- Refresh error types. -/
inductive RefreshDKGError (PartyId : Type*)
  | missingCommit : PartyId → RefreshDKGError PartyId
  | missingShare : PartyId → PartyId → RefreshDKGError PartyId  -- from, to
  | invalidShare : PartyId → RefreshDKGError PartyId
  | thresholdMismatch : Nat → Nat → RefreshDKGError PartyId
  deriving DecidableEq, Repr

/-- Round 3: Aggregate all received shares to compute refresh delta.
    Each party sums: δ_i = f_i(i) + Σⱼ≠ᵢ f_j(i) -/
noncomputable def refreshRound3
    (S : Scheme) [CommRing S.Scalar] [DecidableEq S.PartyId] [DecidableEq S.Public]
    [AddCommGroup S.Public] [Module S.Scalar S.Public]
    [Mul S.Scalar] [Add S.Secret]
    (pidToScalar : S.PartyId → S.Scalar)
    (st : RefreshLocalState S)
    (commits : List (RefreshCommitMsg S))
    (shares : List (RefreshShareMsg S))
    : Except (RefreshDKGError S.PartyId) (RefreshDelta S) := do
  -- Get shares addressed to this party
  let myShares := shares.filter (·.recipient = st.pid)
  -- Verify all received shares
  for shareMsg in myShares do
    if !verifyRefreshShare S pidToScalar commits shareMsg then
      throw (.invalidShare shareMsg.sender)
  -- Compute own share (self-evaluation)
  let ownShare := computeOwnShare S pidToScalar st
  -- Sum all shares: own + received
  let totalDelta := ownShare + (myShares.map (·.share)).sum
  pure { pid := st.pid, delta := totalDelta }

/-!
## Apply Refresh Delta
-/

/-- Apply refresh delta to update a key share.
    new_sk = old_sk + δ
    new_pk = A(new_sk) = old_pk + A(δ)

    The global public key pk is unchanged because Σᵢ δᵢ = 0. -/
def applyRefreshDelta
    (S : Scheme)
    (keyShare : KeyShare S)
    (delta : RefreshDelta S)
    : KeyShare S :=
  let newSk := keyShare.secret + delta.delta
  let newPk := S.A newSk
  KeyShare.create S keyShare.pid newSk newPk keyShare.pk

/-!
## Zero-Sum Verification

The protocol maintains the invariant that Σᵢ δᵢ = 0.
This follows from:
- Each polynomial fⱼ has fⱼ(0) = 0
- δᵢ = Σⱼ fⱼ(i)
- Σᵢ δᵢ = Σᵢ Σⱼ fⱼ(i) = Σⱼ Σᵢ fⱼ(i) = Σⱼ fⱼ(0) · n = 0
  (by properties of polynomial interpolation)
-/

/-- Verify that refresh deltas sum to zero (for testing/auditing). -/
def verifyZeroSum
    (S : Scheme) [DecidableEq S.Secret]
    (deltas : List (RefreshDelta S))
    : Bool :=
  (deltas.map (·.delta)).sum = 0

/-- Zero-sum property as a Prop (for formal proofs). -/
def zeroSumProp
    (S : Scheme)
    (deltas : List (RefreshDelta S))
    : Prop :=
  (deltas.map (·.delta)).sum = 0

end IceNine.Protocol.RefreshDKG
