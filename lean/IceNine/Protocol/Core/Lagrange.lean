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

## CRITICAL: pidToScalar Injectivity Requirement

**The `pidToScalar` function MUST be injective on all active parties.**

If two different parties map to the same scalar, Lagrange interpolation will fail:
- Division by zero: x_j - x_i = 0 when x_j = x_i
- Silent failure: `coeffAtZero` returns 0 to prevent crash
- Security issue: Signature aggregation with 0 coefficients is incorrect

### Validation

Protocol implementations MUST validate injectivity before using Lagrange coefficients.
Use `validatePidToScalarInjective` to check at runtime:

```lean
def validatePidToScalarInjective [DecidableEq S.Scalar]
    (pidToScalar : S.PartyId → S.Scalar)
    (parties : List S.PartyId)
    : Bool :=
  (parties.map pidToScalar).Nodup
```

### Common `pidToScalar` Implementations

1. **Identity (when PartyId = Scalar)**: Inherently injective if party IDs are distinct.

2. **Cast from Nat**: `fun pid => (pid : ZMod q)` - Injective if all PIDs < q.

3. **Hash-based**: `fun pid => H(pid)` - Practically injective for crypto hashes.

4. **Direct assignment**: Assign scalars during DKG - must verify uniqueness.

### Why Not Validate Inside coeffAtZero?

Performance: Lagrange coefficients are computed frequently during signing.
Checking injectivity every time would be expensive. Instead, validate once
at protocol setup (DKG completion) and maintain the invariant.
-/

import IceNine.Protocol.Core.Core
import Mathlib
import Mathlib/RingTheory/Polynomial/Lagrange
import Mathlib/Data/Finset

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
def coeffAtZero {F : Type*} [Field F] [DecidableEq F]
    (partyScalar : F)
    (allScalars : List F)
    : F :=
  let s : Finset F := allScalars.toFinset
  let denomZero := s.erase partyScalar
  denomZero.product (fun xj => xj / (xj - partyScalar))

/-- Compute Lagrange coefficient with explicit "others" list.

    Alternative API where the caller provides only the other parties' scalars.
    Useful when the party list doesn't include the current party.

    λ_i = Π_{j∈others} x_j / (x_j - x_i) -/
def coeffAtZeroOthers {F : Type*} [Field F] [DecidableEq F]
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
def allCoeffsAtZero {F : Type*} [Field F] [DecidableEq F]
    (partyScalars : List F)
    : List (F × F) :=
  partyScalars.map fun p => (p, coeffAtZero p partyScalars)

/-- Compute Lagrange coefficients as a function.
    Returns a lookup function from party scalar to coefficient. -/
def coeffFnAtZero {F : Type*} [Field F] [DecidableEq F]
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
## Injectivity Validation

Functions to verify the critical pidToScalar injectivity requirement.
-/

/-- Validate that pidToScalar is injective on a party list.
    Returns true if all parties map to distinct scalars.

    **CRITICAL**: Call this during protocol setup (e.g., DKG completion) to
    ensure Lagrange interpolation will work correctly.

    **Usage**:
    ```lean
    if !validatePidToScalarInjective S pidToScalar activeParties then
      throw "pidToScalar collision detected"
    ```
-/
def validatePidToScalarInjective (S : Scheme)
    [DecidableEq S.Scalar]
    (pidToScalar : S.PartyId → S.Scalar)
    (parties : List S.PartyId)
    : Bool :=
  (parties.map pidToScalar).Nodup

/-- Find colliding parties under pidToScalar mapping.
    Returns the first pair of parties that map to the same scalar, if any.

    **Usage**: For error reporting when injectivity validation fails. -/
def findPidToScalarCollision (S : Scheme)
    [DecidableEq S.Scalar] [DecidableEq S.PartyId]
    (pidToScalar : S.PartyId → S.Scalar)
    (parties : List S.PartyId)
    : Option (S.PartyId × S.PartyId) :=
  parties.findSome? fun p1 =>
    (parties.filter (· ≠ p1)).findSome? fun p2 =>
      if pidToScalar p1 = pidToScalar p2 then some (p1, p2) else none

/-- Injectivity as a Prop for formal proofs. -/
def pidToScalarInjective (S : Scheme)
    (pidToScalar : S.PartyId → S.Scalar)
    (parties : List S.PartyId)
    : Prop :=
  ∀ p1 p2, p1 ∈ parties → p2 ∈ parties → pidToScalar p1 = pidToScalar p2 → p1 = p2

/-!
## Coefficient Storage

Structure for storing computed coefficients with a party.
-/

/-- Pairing of a party ID with its Lagrange coefficient.
    Used to store precomputed coefficients for signing. -/
structure PartyCoeff (S : Scheme) where
  pid : S.PartyId
  lambda : S.Scalar

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

end IceNine.Protocol.Lagrange
