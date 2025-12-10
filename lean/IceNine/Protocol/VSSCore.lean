/-
# Verifiable Secret Sharing - Core Primitives

Core algebraic structures for Feldman VSS (Verifiable Secret Sharing).
Feldman VSS allows a dealer to distribute shares of a secret such that:
1. Any t shares can reconstruct the secret
2. Each party can verify their share is consistent with the commitment
3. Fewer than t shares reveal nothing about the secret

**Reference**: Feldman, "A Practical Scheme for Non-interactive Verifiable
Secret Sharing", FOCS 1987.
-/

import IceNine.Protocol.Core
import Mathlib

namespace IceNine.Protocol.VSS

open List

/-!
## Power Function

Scalar exponentiation for polynomial evaluation.
-/

/-- Compute x^n for scalars using repeated multiplication. -/
def scalarPow [Monoid M] (x : M) : Nat → M
  | 0 => 1
  | n + 1 => x * scalarPow x n

/-!
## Polynomial Representation

A degree-(t-1) polynomial f(x) = a₀ + a₁x + ... + a_{t-1}x^{t-1}
where a₀ is the secret being shared.
-/

/-- Polynomial represented as list of coefficients [a₀, a₁, ..., a_{t-1}].
    The secret is coeffs[0], threshold is coeffs.length. -/
structure Polynomial (R : Type*) [Semiring R] where
  coeffs : List R
  nonEmpty : coeffs ≠ []
deriving Repr

/-- Degree of polynomial (one less than number of coefficients). -/
def Polynomial.degree {R : Type*} [Semiring R] (p : Polynomial R) : Nat :=
  p.coeffs.length - 1

/-- Threshold for reconstruction (equals number of coefficients). -/
def Polynomial.threshold {R : Type*} [Semiring R] (p : Polynomial R) : Nat :=
  p.coeffs.length

/-- The secret (constant term a₀). -/
def Polynomial.secret {R : Type*} [Semiring R] (p : Polynomial R) : R :=
  p.coeffs.head!

/-- Evaluate polynomial at point x using Horner's method.
    f(x) = a₀ + x(a₁ + x(a₂ + ... + x·a_{t-1})) -/
def Polynomial.eval {R : Type*} [Semiring R] (p : Polynomial R) (x : R) : R :=
  p.coeffs.foldr (fun a acc => a + x * acc) 0

/-- Create polynomial from secret and random coefficients.
    secret is a₀, randoms are [a₁, ..., a_{t-1}]. -/
def mkPolynomial {R : Type*} [Semiring R]
    (secret : R) (randomCoeffs : List R) : Polynomial R :=
  { coeffs := secret :: randomCoeffs
    nonEmpty := by simp }

/-!
## Polynomial Commitment (Feldman)

In Feldman VSS, the dealer commits to each coefficient by publishing g^{a_i}
where g is a generator of a group where discrete log is hard.

For lattice setting, we use A(a_i) where A is the one-way linear map.
-/

/-- Commitment to polynomial coefficients.
    For coefficient a_i, commitment is A(a_i) in lattice setting. -/
structure PolyCommitment (S : Scheme) where
  /-- Commitments to coefficients: [A(a₀), A(a₁), ..., A(a_{t-1})] -/
  commitments : List S.Public
  /-- Threshold (number of coefficients) -/
  threshold : Nat
  /-- Consistency: commitment count matches threshold -/
  consistent : commitments.length = threshold
deriving Repr

/-- Commit to polynomial using scheme's linear map A.
    C_i = A(a_i) for each coefficient. -/
def commitPolynomial (S : Scheme) [Semiring S.Secret] (p : Polynomial S.Secret) : PolyCommitment S :=
  { commitments := p.coeffs.map S.A
    threshold := p.threshold
    consistent := by simp [Polynomial.threshold, List.length_map] }

/-!
## Share Generation

A share for party j is (j, f(j)) where f is the polynomial.
The evaluation point j is typically derived from the party ID.
-/

/-- A VSS share: evaluation point and value. -/
structure VSSShare (S : Scheme) where
  /-- Party receiving this share -/
  recipient : S.PartyId
  /-- Evaluation point (typically derived from party ID) -/
  evalPoint : S.Scalar
  /-- Share value: f(evalPoint) -/
  value : S.Secret
deriving Repr

/-- Generate share for a party at given evaluation point. -/
def generateShare (S : Scheme) [Monoid S.Scalar] [Module S.Scalar S.Secret]
    (p : Polynomial S.Secret) (recipient : S.PartyId) (evalPoint : S.Scalar)
    : VSSShare S :=
  { recipient := recipient
    evalPoint := evalPoint
    value := evalPolynomialScalar S p evalPoint }
where
  /-- Evaluate polynomial with scalar multiplication. -/
  evalPolynomialScalar (S : Scheme) [Monoid S.Scalar] [Module S.Scalar S.Secret]
      (p : Polynomial S.Secret) (x : S.Scalar) : S.Secret :=
    -- f(x) = Σ_{i=0}^{t-1} a_i · x^i
    let indexed := p.coeffs.enum
    indexed.foldl (fun acc (i, a) =>
      let xPowI := scalarPow x i  -- x^i
      acc + xPowI • a) 0

/-- Generate shares for all parties. -/
def generateShares (S : Scheme) [Monoid S.Scalar] [Module S.Scalar S.Secret]
    (p : Polynomial S.Secret)
    (parties : List (S.PartyId × S.Scalar))  -- (party, eval point) pairs
    : List (VSSShare S) :=
  parties.map fun (pid, pt) => generateShare S p pid pt

/-!
## Share Verification

Party j verifies their share s_j against the commitment by checking:
  A(s_j) = Σ_{i=0}^{t-1} (j^i) · C_i

In group notation: g^{s_j} = Π_{i=0}^{t-1} C_i^{j^i}

This works because:
  A(s_j) = A(f(j)) = A(Σ a_i · j^i) = Σ j^i · A(a_i) = Σ j^i · C_i
-/

/-- Compute expected public value from commitment and evaluation point.
    Returns Σ_{i=0}^{t-1} (x^i) · C_i -/
def expectedPublicValue (S : Scheme) [Monoid S.Scalar] [Module S.Scalar S.Public]
    (comm : PolyCommitment S) (evalPoint : S.Scalar) : S.Public :=
  let indexed := comm.commitments.enum
  List.foldl (fun acc (i, c) =>
    let xPowI := scalarPow evalPoint i  -- x^i
    acc + xPowI • c) 0 indexed

/-- Verify a share against the polynomial commitment.
    Checks: A(share.value) = expectedPublicValue(commitment, share.evalPoint) -/
def verifyShare (S : Scheme) [Monoid S.Scalar] [Module S.Scalar S.Public]
    (comm : PolyCommitment S) (share : VSSShare S) : Prop :=
  S.A share.value = expectedPublicValue S comm share.evalPoint

/-- Decidable share verification (requires decidable equality on Public). -/
def verifyShareBool (S : Scheme) [Monoid S.Scalar] [Module S.Scalar S.Public] [DecidableEq S.Public]
    (comm : PolyCommitment S) (share : VSSShare S) : Bool :=
  S.A share.value == expectedPublicValue S comm share.evalPoint

/-!
## VSS Transcript

Complete transcript of a VSS dealing, including commitment and all shares.
-/

/-- Evaluation points of shares are distinct.
    This is essential for Lagrange interpolation to work correctly. -/
def evalPointsDistinct {S : Scheme} [DecidableEq S.Scalar]
    (shares : List (VSSShare S)) : Prop :=
  (shares.map (·.evalPoint)).Nodup

/-- Decidable check for distinct eval points. -/
def evalPointsDistinctBool {S : Scheme} [DecidableEq S.Scalar]
    (shares : List (VSSShare S)) : Bool :=
  (shares.map (·.evalPoint)).Nodup

/-- Complete VSS dealing transcript.

    **Invariants**:
    - `commitment.threshold` equals the polynomial degree + 1
    - All shares have distinct evaluation points (required for interpolation)
    - Each share verifies against the commitment -/
structure VSSTranscript (S : Scheme) [DecidableEq S.Scalar] where
  /-- Polynomial commitment (public) -/
  commitment : PolyCommitment S
  /-- Shares distributed to parties (each share sent privately) -/
  shares : List (VSSShare S)
  /-- All shares have distinct evaluation points -/
  evalPointsNodup : evalPointsDistinct shares
deriving Repr

/-- Create VSS transcript from polynomial and party list.
    Requires that party evaluation points are distinct. -/
def createVSSTranscript (S : Scheme) [DecidableEq S.Scalar] [Semiring S.Secret] [Monoid S.Scalar] [Module S.Scalar S.Secret]
    (p : Polynomial S.Secret)
    (parties : List (S.PartyId × S.Scalar))
    (hnodup : (parties.map Prod.snd).Nodup)
    : VSSTranscript S :=
  { commitment := commitPolynomial S p
    shares := generateShares S p parties
    evalPointsNodup := by
      -- shares.map evalPoint = parties.map snd
      simp only [evalPointsDistinct, generateShares, List.map_map]
      -- generateShare preserves evalPoint from input
      have h : (parties.map fun (pid, pt) => (generateShare S p pid pt).evalPoint) =
               parties.map Prod.snd := by
        apply List.map_congr
        intro (pid, pt) _
        simp only [generateShare]
        rfl
      rw [h]
      exact hnodup
  }

/-- Try to create VSS transcript with runtime check for distinct eval points. -/
def tryCreateVSSTranscript (S : Scheme) [DecidableEq S.Scalar] [Semiring S.Secret] [Monoid S.Scalar] [Module S.Scalar S.Secret]
    (p : Polynomial S.Secret)
    (parties : List (S.PartyId × S.Scalar))
    : Option (VSSTranscript S) :=
  if h : (parties.map Prod.snd).Nodup then
    some (createVSSTranscript S p parties h)
  else
    none

end IceNine.Protocol.VSS
