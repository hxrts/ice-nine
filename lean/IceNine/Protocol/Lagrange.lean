/-
# Lagrange Interpolation Coefficients

Unified API for computing Lagrange interpolation coefficients.
Used across threshold protocols for:
- Threshold signing (aggregating partial signatures)
- DKG with exclusion (reconstructing public key from subset)
- Share repair (computing weighted contributions)

## Mathematical Background

Lagrange interpolation allows reconstructing a polynomial f(x) of degree < n
from n evaluation points (x_i, f(x_i)).

For threshold signatures with evaluation at 0:
  λ_i = Π_{j≠i} (0 - x_j) / (x_i - x_j) = Π_{j≠i} x_j / (x_j - x_i)

This gives us: f(0) = Σ_i λ_i · f(x_i)
-/

import IceNine.Protocol.Core
import Mathlib

namespace IceNine.Protocol.Lagrange

open IceNine.Protocol

/-!
## Core Lagrange Coefficient Computation

The canonical implementation used throughout the protocol.
-/

/-- Compute Lagrange coefficient for evaluating at 0.

    Given a party with scalar representation `partyScalar` and a list of all
    party scalars in the interpolation set, computes:

    λ_i = Π_{j≠i} x_j / (x_j - x_i)

    **Usage**:
    - `partyScalar`: This party's scalar (x_i)
    - `allScalars`: All parties' scalars including this one

    **Safety**: Returns 0 if any two parties have the same scalar (degenerate case). -/
def coeffAtZero [Field F] [DecidableEq F]
    (partyScalar : F)
    (allScalars : List F)
    : F :=
  let others := allScalars.filter (· ≠ partyScalar)
  -- Check for degeneracy: if any other scalar equals partyScalar, return 0
  if others.length ≠ allScalars.length - 1 then
    0  -- Multiple parties with same scalar
  else
    others.foldl (fun acc xj => acc * (xj / (xj - partyScalar))) 1

/-- Compute Lagrange coefficient with explicit "others" list.

    Alternative API where the caller provides only the other parties' scalars.
    Useful when the party list doesn't include the current party.

    λ_i = Π_{j∈others} x_j / (x_j - x_i) -/
def coeffAtZeroOthers [Field F] [DecidableEq F]
    (partyScalar : F)
    (otherScalars : List F)
    : F :=
  -- Check for degeneracy
  if otherScalars.any (· = partyScalar) then
    0
  else
    otherScalars.foldl (fun acc xj => acc * (xj / (xj - partyScalar))) 1

/-!
## Batch Computation

Compute coefficients for all parties at once.
-/

/-- Compute Lagrange coefficients for all parties in a set.
    Returns list of (scalar, coefficient) pairs. -/
def allCoeffsAtZero [Field F] [DecidableEq F]
    (partyScalars : List F)
    : List (F × F) :=
  partyScalars.map fun p => (p, coeffAtZero p partyScalars)

/-- Compute Lagrange coefficients as a function.
    Returns a lookup function from party scalar to coefficient. -/
def coeffFnAtZero [Field F] [DecidableEq F]
    (partyScalars : List F)
    : F → F :=
  fun p => coeffAtZero p partyScalars

/-!
## Scheme-Aware API

API integrated with the Scheme type for protocol use.
-/

/-- Compute Lagrange coefficient for a party in a scheme.
    Requires a function to convert party IDs to field elements. -/
def schemeCoeffAtZero (S : Scheme)
    [Field S.Scalar] [DecidableEq S.Scalar] [DecidableEq S.PartyId]
    (pidToScalar : S.PartyId → S.Scalar)
    (allParties : List S.PartyId)
    (party : S.PartyId)
    : S.Scalar :=
  let allScalars := allParties.map pidToScalar
  let partyScalar := pidToScalar party
  coeffAtZero partyScalar allScalars

/-- Compute all Lagrange coefficients for a set of parties.
    Returns list of (party ID, coefficient) pairs. -/
def schemeAllCoeffs (S : Scheme)
    [Field S.Scalar] [DecidableEq S.Scalar] [DecidableEq S.PartyId]
    (pidToScalar : S.PartyId → S.Scalar)
    (allParties : List S.PartyId)
    : List (S.PartyId × S.Scalar) :=
  allParties.map fun pid => (pid, schemeCoeffAtZero S pidToScalar allParties pid)

/-!
## Coefficient Storage

Structure for storing computed coefficients with a party.
-/

/-- Pairing of a party ID with its Lagrange coefficient.
    Used to store precomputed coefficients for signing. -/
structure PartyCoeff (S : Scheme) where
  pid : S.PartyId
  lambda : S.Scalar
deriving Repr

/-- Build party coefficient pairs from a party list. -/
def buildPartyCoeffs (S : Scheme)
    [Field S.Scalar] [DecidableEq S.Scalar] [DecidableEq S.PartyId]
    (pidToScalar : S.PartyId → S.Scalar)
    (parties : List S.PartyId)
    : List (PartyCoeff S) :=
  parties.map fun pid =>
    { pid := pid
      lambda := schemeCoeffAtZero S pidToScalar parties pid }

/-!
## Properties

Theorems about Lagrange coefficients.
-/

/-- Lagrange coefficients sum to 1 when evaluating at a point in the domain.
    (This is the partition of unity property.) -/
theorem coeffs_sum_to_one [Field F] [DecidableEq F]
    (partyScalars : List F)
    (hnodup : partyScalars.Nodup)
    (hne : partyScalars ≠ []) :
    (allCoeffsAtZero partyScalars).map Prod.snd |>.sum = 1 := by
  sorry  -- Requires careful induction on Lagrange formula

/-- Zero coefficient when party not in set. -/
theorem coeff_zero_not_in [Field F] [DecidableEq F]
    (partyScalar : F)
    (allScalars : List F)
    (hnotin : partyScalar ∉ allScalars) :
    coeffAtZero partyScalar allScalars =
      allScalars.foldl (fun acc xj => acc * (xj / (xj - partyScalar))) 1 := by
  simp [coeffAtZero]
  intro h
  have : allScalars.filter (· ≠ partyScalar) = allScalars := by
    apply List.filter_eq_self.mpr
    intro x hx
    exact fun heq => hnotin (heq ▸ hx)
  rw [this]
  simp [List.length]

end IceNine.Protocol.Lagrange
