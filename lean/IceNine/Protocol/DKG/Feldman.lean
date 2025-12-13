/-
# Feldman VSS

Core algebraic structures for Feldman VSS (Verifiable Secret Sharing).
Feldman VSS allows a dealer to distribute shares of a secret such that:
1. Any t shares can reconstruct the secret
2. Each party can verify their share is consistent with the commitment
3. Fewer than t shares reveal nothing about the secret

**Reference**: Feldman, "A Practical Scheme for Non-interactive Verifiable
Secret Sharing", FOCS 1987.
-/

import IceNine.Protocol.Core.Core
import Mathlib
import Mathlib.Algebra.Polynomial.Module.Basic

namespace IceNine.Protocol.VSS

open List

/-!
## Polynomials via `PolynomialModule`

We model VSS polynomials as finitely supported coefficient sequences
(`PolynomialModule S.Scalar S.Secret = ℕ →₀ S.Secret`). This avoids requiring a
`Semiring` structure on `S.Secret` while still giving us Mathlib's evaluation
and mapping lemmas.
-/

/-- Secret polynomials (coefficients in `S.Secret`). -/
abbrev SecretPoly (S : Scheme) [CommRing S.Scalar]
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret] :=
  PolynomialModule S.Scalar S.Secret

/-- Commitment polynomials (coefficients in `S.Public`). -/
abbrev PublicPoly (S : Scheme) [CommRing S.Scalar]
    [AddCommGroup S.Public] [Module S.Scalar S.Public] :=
  PolynomialModule S.Scalar S.Public

/-- Build a polynomial module element from a coefficient list `[a₀, a₁, ...]`. -/
noncomputable def polyOfList {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (coeffs : List M) : PolynomialModule R M :=
  let rec go (i : Nat) (cs : List M) : PolynomialModule R M :=
    match cs with
    | [] => 0
    | c :: cs => PolynomialModule.single R i c + go (i + 1) cs
  go 0 coeffs

/-- Create the degree-(t-1) polynomial with constant term `secret`.
    `randomCoeffs` are `[a₁, ..., a_{t-1}]`. -/
noncomputable def mkPolynomial (S : Scheme) [CommRing S.Scalar]
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    (secret : S.Secret) (randomCoeffs : List S.Secret) : SecretPoly S :=
  polyOfList (secret :: randomCoeffs)

/-!
## Polynomial Commitment (Feldman)

In Feldman VSS, the dealer commits to each coefficient by publishing g^{a_i}
where g is a generator of a group where discrete log is hard.

For Ice Nine, we use A(a_i) where A is the one-way linear map.
-/

/-- Commitment to polynomial coefficients, as a commitment polynomial
    (coefficient-wise application of `A`). -/
structure PolyCommitment (S : Scheme) [CommRing S.Scalar]
    [AddCommGroup S.Public] [Module S.Scalar S.Public] where
  /-- Commitment polynomial with coefficients `[A(a₀), A(a₁), ...]`. -/
  poly : PublicPoly S
  /-- Threshold (degree bound + 1). -/
  threshold : Nat

/-- Commit to a secret polynomial by mapping coefficients through `A`. -/
noncomputable def commitPolynomial (S : Scheme) [CommRing S.Scalar]
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [AddCommGroup S.Public] [Module S.Scalar S.Public]
    (p : SecretPoly S) (threshold : Nat) : PolyCommitment S :=
  { poly := PolynomialModule.map S.A p
    threshold := threshold }

/-- Commit directly from a coefficient list `[a₀, ..., a_{t-1}]`. -/
noncomputable def commitPolynomialFromCoeffs (S : Scheme) [CommRing S.Scalar]
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [AddCommGroup S.Public] [Module S.Scalar S.Public]
    (coeffs : List S.Secret) : PolyCommitment S :=
  commitPolynomial S (polyOfList coeffs) coeffs.length

/-!
## Share Generation

A share for party j is (j, f(j)) where f is the secret polynomial.
-/

/-- A VSS share: evaluation point and value. -/
structure VSSShare (S : Scheme) where
  /-- Party receiving this share. -/
  recipient : S.PartyId
  /-- Evaluation point (typically derived from party ID). -/
  evalPoint : S.Scalar
  /-- Share value: f(evalPoint). -/
  value : S.Secret

/-- Generate share for a party at a given evaluation point. -/
noncomputable def generateShare (S : Scheme) [CommRing S.Scalar]
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    (p : SecretPoly S) (recipient : S.PartyId) (evalPoint : S.Scalar)
    : VSSShare S :=
  { recipient := recipient
    evalPoint := evalPoint
    value := PolynomialModule.eval evalPoint p }

/-- Generate shares for all parties. -/
noncomputable def generateShares (S : Scheme) [CommRing S.Scalar]
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    (p : SecretPoly S)
    (parties : List (S.PartyId × S.Scalar))  -- (party, eval point) pairs
    : List (VSSShare S) :=
  parties.map fun (pid, pt) => generateShare S p pid pt

/-!
## Share Verification

Party j verifies their share s_j against the commitment by checking:

  A(s_j) = Σ (x^i) • C_i

where `C_i` are the committed coefficients and `x` is the party's evaluation point.

This works because `A` is linear:

  A(f(x)) = A(Σ a_i • x^i) = Σ x^i • A(a_i).
-/

/-- Compute expected public value from a commitment and an evaluation point.
    Returns `Σ (x^i) • C_i` by evaluating the commitment polynomial. -/
noncomputable def expectedPublicValue (S : Scheme) [CommRing S.Scalar]
    [AddCommGroup S.Public] [Module S.Scalar S.Public]
    (comm : PolyCommitment S) (evalPoint : S.Scalar) : S.Public :=
  PolynomialModule.eval evalPoint comm.poly

/-- Verify a share against the polynomial commitment.
    Checks: `A(share.value) = expectedPublicValue(commitment, share.evalPoint)`. -/
def verifyShare (S : Scheme) [CommRing S.Scalar]
    [AddCommGroup S.Public] [Module S.Scalar S.Public]
    (comm : PolyCommitment S) (share : VSSShare S) : Prop :=
  S.A share.value = expectedPublicValue S comm share.evalPoint

/-- Decidable share verification (requires decidable equality on Public). -/
noncomputable def verifyShareBool (S : Scheme) [CommRing S.Scalar]
    [AddCommGroup S.Public] [Module S.Scalar S.Public] [DecidableEq S.Public]
    (comm : PolyCommitment S) (share : VSSShare S) : Bool :=
  decide (verifyShare S comm share)

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

/-- Complete VSS dealing transcript. -/
structure VSSTranscript (S : Scheme) [CommRing S.Scalar] [DecidableEq S.Scalar]
    [AddCommGroup S.Public] [Module S.Scalar S.Public] where
  /-- Polynomial commitment (public). -/
  commitment : PolyCommitment S
  /-- Shares distributed to parties (each share sent privately). -/
  shares : List (VSSShare S)
  /-- All shares have distinct evaluation points. -/
  evalPointsNodup : evalPointsDistinct shares

/-- Helper lemma: generateShare preserves evalPoint. -/
theorem generateShare_evalPoint (S : Scheme) [CommRing S.Scalar]
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    (p : SecretPoly S) (pid : S.PartyId) (pt : S.Scalar) :
    (generateShare S p pid pt).evalPoint = pt := rfl

/-- Helper lemma: generateShares preserves eval points in order. -/
theorem generateShares_evalPoints (S : Scheme) [CommRing S.Scalar] [DecidableEq S.Scalar]
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    (p : SecretPoly S)
    (parties : List (S.PartyId × S.Scalar)) :
    (generateShares S p parties).map (·.evalPoint) = parties.map Prod.snd := by
  induction parties with
  | nil => rfl
  | cons hd tl ih =>
    simp only [generateShares, List.map_cons, List.map]
    rw [ih]

/-- Create VSS transcript from a polynomial and party list.
    Requires that party evaluation points are distinct. -/
noncomputable def createVSSTranscript (S : Scheme) [CommRing S.Scalar] [DecidableEq S.Scalar]
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [AddCommGroup S.Public] [Module S.Scalar S.Public]
    (p : SecretPoly S) (threshold : Nat)
    (parties : List (S.PartyId × S.Scalar))
    (hnodup : (parties.map Prod.snd).Nodup)
    : VSSTranscript S :=
  { commitment := commitPolynomial S p threshold
    shares := generateShares S p parties
    evalPointsNodup := by
      simp only [evalPointsDistinct]
      rw [generateShares_evalPoints]
      exact hnodup }

/-- Try to create VSS transcript with runtime check for distinct eval points. -/
noncomputable def tryCreateVSSTranscript (S : Scheme) [CommRing S.Scalar] [DecidableEq S.Scalar]
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [AddCommGroup S.Public] [Module S.Scalar S.Public]
    (p : SecretPoly S) (threshold : Nat)
    (parties : List (S.PartyId × S.Scalar))
    : Option (VSSTranscript S) :=
  if h : (parties.map Prod.snd).Nodup then
    some (createVSSTranscript S p threshold parties h)
  else
    none

end IceNine.Protocol.VSS
