/-
# Threshold DKG

Complaint-based DKG for t-of-n threshold signing. Instead of aborting on
first error, collects complaints against misbehaving parties. Enables
exclusion of bad actors while continuing with honest majority.
Security proofs in `Security/DKG`.
-/

import IceNine.Protocol.DKGCore
import Mathlib

namespace IceNine.Protocol

open List

/-!
## Complaints

When a party misbehaves (invalid commitment or missing reveal),
other parties can file a complaint identifying the offender.
-/

/-- Complaint types identifying misbehaving parties. -/
inductive Complaint (PartyId : Type u) where
  | openingMismatch (accused : PartyId)  -- reveal doesn't match commitment
  | missingReveal (accused : PartyId)    -- party committed but never revealed
  deriving DecidableEq

/-!
## Complaint Collection

Walk through all commit-reveal pairs and collect any mismatches.
Returns empty list if all parties behaved honestly.
-/

/-- Check all pairs and collect complaints for any mismatches.
    Does not short-circuit: finds ALL misbehaving parties. -/
def dkgCheckComplaints
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  : List (Complaint S.PartyId) :=
  let pairs := List.zip commits reveals
  pairs.foldl
    (fun acc (c,r) =>
      -- Check party ID matches between commit and reveal
      if hpid : c.sender = r.sender then
        -- Check revealed value opens commitment correctly
        if hcom : S.commit r.pk_i r.opening = c.commitPk then acc
        else Complaint.openingMismatch r.sender :: acc
      else Complaint.openingMismatch r.sender :: acc)
    []

/-!
## Aggregation with Complaints

Returns either the public key (if no complaints) or the list of
complaints (if any party misbehaved). Caller decides how to handle.
-/

/-- Aggregate with complaint collection instead of immediate abort.
    Ok(pk) if all valid, Error(complaints) if any invalid. -/
def dkgAggregateWithComplaints
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  : Except (List (Complaint S.PartyId)) S.Public :=
  -- First check lengths match
  if hlen : commits.length = reveals.length then
    -- Collect all complaints
    let cs := dkgCheckComplaints S commits reveals
    if hnil : cs = [] then
      -- No complaints: compute pk = Σ pk_i
      let pk := (reveals.map (·.pk_i)).sum
      Except.ok pk
    else
      -- Return complaints for blame attribution
      Except.error cs
  else
    -- Length mismatch: someone didn't reveal
    Except.error [Complaint.missingReveal (commits.head?.map (·.sender)).getD (reveals.head?.map (·.sender)).getD (default)]

/-!
## Party Exclusion

After complaints are collected, we can compute which parties should be
excluded from the protocol. The remaining "valid" parties can continue
if there are enough for threshold security.
-/

/-- Extract the accused party from a complaint -/
def Complaint.accused : Complaint PartyId → PartyId
  | .openingMismatch p => p
  | .missingReveal p => p

/-- Get all parties accused in a list of complaints -/
def accusedParties [DecidableEq PartyId]
    (complaints : List (Complaint PartyId)) : List PartyId :=
  (complaints.map Complaint.accused).dedup

/-- Remove faulty parties from participant list -/
def excludeFaulty [DecidableEq PartyId]
    (allParties : List PartyId)
    (complaints : List (Complaint PartyId)) : List PartyId :=
  let faulty := accusedParties complaints
  allParties.filter (fun p => p ∉ faulty)

/-- Check if enough valid parties remain for threshold security -/
def hasThresholdQuorum [DecidableEq PartyId]
    (allParties : List PartyId)
    (complaints : List (Complaint PartyId))
    (threshold : Nat) : Bool :=
  (excludeFaulty allParties complaints).length ≥ threshold

/-- Result of party exclusion check -/
inductive ExclusionResult (PartyId : Type u)
  | quorumMet (validParties : List PartyId)  -- enough honest parties remain
  | quorumFailed (validCount : Nat) (needed : Nat)  -- too many faulty
  deriving Repr

/-- Compute valid party set and check if threshold is met -/
def computeValidParties [DecidableEq PartyId]
    (allParties : List PartyId)
    (complaints : List (Complaint PartyId))
    (threshold : Nat) : ExclusionResult PartyId :=
  let valid := excludeFaulty allParties complaints
  if valid.length ≥ threshold then
    .quorumMet valid
  else
    .quorumFailed valid.length threshold

/-!
## Reconstruction from Subset

When some parties are excluded, the remaining valid parties can still
generate a threshold key using Lagrange interpolation on their shares.

For t-of-n threshold: if at least t parties are valid, they can reconstruct.
-/

/-- Filter reveals to only include valid (non-faulty) parties -/
def filterValidReveals [DecidableEq S.PartyId]
    (reveals : List (DkgRevealMsg S))
    (validParties : List S.PartyId) : List (DkgRevealMsg S) :=
  reveals.filter (fun r => r.sender ∈ validParties)

/-- Filter commits to only include valid parties -/
def filterValidCommits [DecidableEq S.PartyId]
    (commits : List (DkgCommitMsg S))
    (validParties : List S.PartyId) : List (DkgCommitMsg S) :=
  commits.filter (fun c => c.sender ∈ validParties)

/-- Lagrange coefficient for party i evaluating at 0.
    λ_i = Π_{j∈S, j≠i} x_j / (x_j - x_i)
    Used for reconstructing from subset of parties. -/
def dkgLagrangeCoeff [Field F] [DecidableEq F]
    (pidToScalar : PartyId → F)
    (validPids : List PartyId)
    (i : PartyId) : F :=
  let xi := pidToScalar i
  let others := validPids.filter (· ≠ i)
  if others.any (fun j => pidToScalar j = xi) then 0  -- degenerate case
  else (others.map (fun j => let xj := pidToScalar j; xj / (xj - xi))).prod

/-- Reconstruct public key from subset using Lagrange interpolation.

    If parties hold shares of a degree-(t-1) polynomial f where:
    - pk_i = f(i) for each party i
    - pk = f(0) is the combined public key

    Then: pk = Σ_{i∈S} λ_i · pk_i where S is any t-sized subset
    and λ_i are the Lagrange coefficients for evaluating at 0. -/
def reconstructPkFromSubset
    (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
    (pidToScalar : S.PartyId → S.Scalar)
    (validReveals : List (DkgRevealMsg S)) : S.Public :=
  let validPids := validReveals.map (·.sender)
  let weightedPks := validReveals.map fun r =>
    let λ_i := dkgLagrangeCoeff pidToScalar validPids r.sender
    λ_i • r.pk_i
  weightedPks.sum

/-- Full DKG with complaint handling and reconstruction from valid subset.

    Returns:
    - Ok(pk, validParties) if threshold met with valid subset
    - Error(complaints, validCount) if too many faulty parties -/
def dkgWithExclusion
    (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
    (pidToScalar : S.PartyId → S.Scalar)
    (allParties : List S.PartyId)
    (commits : List (DkgCommitMsg S))
    (reveals : List (DkgRevealMsg S))
    (threshold : Nat)
    : Except (List (Complaint S.PartyId) × Nat) (S.Public × List S.PartyId) :=
  -- Collect complaints
  let complaints := dkgCheckComplaints S commits reveals
  if complaints.isEmpty then
    -- No complaints: simple aggregation (n-of-n case)
    let pk := (reveals.map (·.pk_i)).sum
    Except.ok (pk, allParties)
  else
    -- Some parties misbehaved: try reconstruction from valid subset
    let validParties := excludeFaulty allParties complaints
    if validParties.length ≥ threshold then
      -- Enough valid parties: reconstruct using Lagrange
      let validReveals := filterValidReveals reveals validParties
      let pk := reconstructPkFromSubset S pidToScalar validReveals
      Except.ok (pk, validParties)
    else
      -- Not enough valid parties: report failure
      Except.error (complaints, validParties.length)

/-!
## Threshold Security Requirement

For the DKG to be secure, we need:
- Total parties: n
- Threshold: t (minimum signers needed)
- Faulty tolerance: n - t (max parties that can be excluded)

If more than n - t parties are faulty, the protocol must abort.
-/

/-- Check threshold security requirement -/
def checkThresholdSecurity
    (totalParties : Nat)
    (threshold : Nat)
    (faultyCount : Nat) : Bool :=
  faultyCount ≤ totalParties - threshold

/-- Threshold DKG parameters -/
structure DKGParams where
  /-- Total number of parties -/
  n : Nat
  /-- Minimum signers needed (threshold) -/
  t : Nat
  /-- t ≤ n required -/
  threshold_valid : t ≤ n

/-- Maximum tolerable faulty parties -/
def DKGParams.maxFaulty (p : DKGParams) : Nat := p.n - p.t

/-- Check if DKG can continue given faulty count -/
def DKGParams.canContinue (p : DKGParams) (faultyCount : Nat) : Bool :=
  faultyCount ≤ p.maxFaulty

end IceNine.Protocol
