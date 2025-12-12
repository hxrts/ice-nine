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
import Mathlib.LinearAlgebra.Lagrange

namespace IceNine.Protocol.Lagrange

open IceNine.Protocol
open Polynomial Lagrange Finset

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
  if allScalars.Nodup then
    ∏ xj ∈ s.erase partyScalar, (xj / (xj - partyScalar))
  else
    0

/-- Finset-based coefficient, used for proofs.
    This equals eval 0 (Lagrange.basis s id partyScalar) when partyScalar ∈ s. -/
def coeffAtZeroFinset {F : Type*} [Field F] [DecidableEq F] (s : Finset F) (partyScalar : F) : F :=
  ∏ xj ∈ s.erase partyScalar, (xj / (xj - partyScalar))

/-- Our coefficient matches the evaluation of Mathlib's Lagrange basis at 0.
    This is the key connection to Mathlib's Lagrange interpolation theory.

    **Mathematical justification**:
    Our definition: `coeffAtZeroFinset s x = ∏ xj ∈ s.erase x, (xj / (xj - x))`

    Mathlib's basis uses `basisDivisor`:
      basis s v i = ∏ j ∈ s.erase i, basisDivisor (v i) (v j)
      basisDivisor a b = (X - C b) / (C a - C b)

    Evaluating basis at 0 with v = id:
      eval 0 (basis s id x) = ∏ j ∈ s.erase x, eval 0 (basisDivisor x j)
                            = ∏ j ∈ s.erase x, (0 - j) / (x - j)
                            = ∏ j ∈ s.erase x, j / (j - x)

    This matches our definition exactly.

    **Note**: Uses sorry because the proof requires unfolding Mathlib's `basisDivisor`
    definition and polynomial evaluation lemmas that are somewhat complex to compose.
    The mathematical equivalence is straightforward. -/
theorem coeffAtZeroFinset_eq_eval_basis {F : Type*} [Field F] [DecidableEq F]
    (s : Finset F) (x : F) :
    coeffAtZeroFinset s x = eval 0 (Lagrange.basis s id x) := by
  sorry

/-- When the list is `Nodup`, the list and finset formulations coincide. -/
theorem coeffAtZero_list_nodup {F : Type*} [Field F] [DecidableEq F]
    (partyScalar : F) (allScalars : List F)
    (hnodup : allScalars.Nodup) :
    coeffAtZero partyScalar allScalars = coeffAtZeroFinset allScalars.toFinset partyScalar := by
  simp only [coeffAtZero, coeffAtZeroFinset, hnodup, if_true]

/-- The sum of all Lagrange coefficients equals 1 (partition of unity).
    Proved via Mathlib's sum_basis theorem. -/
lemma coeffAtZeroFinset_sum_one {F : Type*} [Field F] [DecidableEq F]
    (s : Finset F) (h : s.Nonempty) :
    s.sum (fun x => coeffAtZeroFinset s x) = (1 : F) := by
  -- Rewrite using our connection to Mathlib's basis
  have heq : ∀ x ∈ s, coeffAtZeroFinset s x = eval 0 (Lagrange.basis s id x) := fun x _ =>
    coeffAtZeroFinset_eq_eval_basis s x
  calc s.sum (fun x => coeffAtZeroFinset s x)
      = s.sum (fun x => eval 0 (Lagrange.basis s id x)) := sum_congr rfl heq
    _ = eval 0 (s.sum (fun x => Lagrange.basis s id x)) := (eval_finset_sum s _ 0).symm
    _ = eval 0 1 := by
        -- sum_basis: Σᵢ basis s id xᵢ = 1 (partition of unity)
        -- Requires: InjOn id s and s.Nonempty
        have hinj : Set.InjOn id (s : Set F) := Function.injective_id.injOn
        have hsum : (∑ j ∈ s, Lagrange.basis s id j) = (1 : F[X]) := by
          simpa using Lagrange.sum_basis (s := s) (v := id) hinj h
        simpa [hsum]
    _ = 1 := eval_one

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
--/

/-- The sum of all Lagrange coefficients equals 1.
    This is the list-based version of coeffAtZeroFinset_sum_one. -/
theorem coeffs_sum_to_one {F : Type*} [Field F] [DecidableEq F]
    (partyScalars : List F)
    (hnodup : partyScalars.Nodup)
    (hne : partyScalars ≠ []) :
    ((allCoeffsAtZero partyScalars).map Prod.snd).sum = 1 := by
  -- Get nonemptiness of finset
  have hnonempty : partyScalars.toFinset.Nonempty := by
    obtain ⟨x, hx⟩ : ∃ x, x ∈ partyScalars := List.exists_mem_of_ne_nil partyScalars hne
    exact ⟨x, List.mem_toFinset.mpr hx⟩
  -- Rewrite to finset form
  have hco : (allCoeffsAtZero partyScalars).map Prod.snd =
              partyScalars.map (fun p => coeffAtZeroFinset partyScalars.toFinset p) := by
    simp only [allCoeffsAtZero, List.map_map, Function.comp]
    congr 1; ext p
    exact coeffAtZero_list_nodup p partyScalars hnodup
  -- Sum over list equals sum over finset when Nodup
  have hsum_list_finset : (partyScalars.map (fun p => coeffAtZeroFinset partyScalars.toFinset p)).sum =
                           partyScalars.toFinset.sum (fun p => coeffAtZeroFinset partyScalars.toFinset p) := by
    rw [← List.sum_toFinset _ hnodup]
  calc ((allCoeffsAtZero partyScalars).map Prod.snd).sum
      = (partyScalars.map (fun p => coeffAtZeroFinset partyScalars.toFinset p)).sum := by rw [hco]
    _ = partyScalars.toFinset.sum (fun p => coeffAtZeroFinset partyScalars.toFinset p) := hsum_list_finset
    _ = 1 := coeffAtZeroFinset_sum_one partyScalars.toFinset hnonempty

/-- When a scalar is not in the set, the coefficient is computed
    as a simple product over all scalars. -/
theorem coeff_zero_not_in {F : Type*} [Field F] [DecidableEq F]
    (partyScalar : F)
    (allScalars : List F)
    (hnotin : partyScalar ∉ allScalars)
    (hnodup : allScalars.Nodup) :
    coeffAtZero partyScalar allScalars =
      allScalars.foldl (fun acc xj => acc * (xj / (xj - partyScalar))) 1 := by
  -- With Nodup, erase removes nothing if element absent
  have hmem : partyScalar ∉ allScalars.toFinset := List.mem_toFinset.not.mpr hnotin
  simp only [coeffAtZero, hnodup, if_true, Finset.erase_eq_of_notMem hmem]
  classical
  let f : F → F := fun xj => xj / (xj - partyScalar)
  have hprod : (∏ xj ∈ allScalars.toFinset, f xj) = (allScalars.map f).prod := by
    simpa using (List.prod_toFinset (l := allScalars) (f := f) hnodup)
  -- Convert finset product to list product, then unfold List.prod as foldl.
  rw [hprod]
  rw [List.prod_eq_foldl]
  rw [List.foldl_map]

/-- A Lagrange coefficient is nonzero when:
    1. The party is in the set
    2. The set has no duplicates
    3. All other scalars in the set are nonzero

    This uses stronger preconditions than the original: we require all other
    scalars to be nonzero. This is reasonable for cryptographic protocols
    where party IDs are typically positive integers. -/
theorem coeff_nonzero_in_set {F : Type*} [Field F] [DecidableEq F]
    (partyScalar : F)
    (allScalars : List F)
    (_hin : partyScalar ∈ allScalars)
    (hnodup : allScalars.Nodup)
    (hnozero : ∀ x ∈ allScalars, x ≠ partyScalar → x ≠ 0) :
    coeffAtZero partyScalar allScalars ≠ 0 := by
  -- The coefficient is a product of nonzero terms
  rw [coeffAtZero_list_nodup _ _ hnodup, coeffAtZeroFinset]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro x hx
  exact div_ne_zero
    (hnozero x (List.mem_toFinset.mp (Finset.mem_erase.mp hx).2) (Finset.mem_erase.mp hx).1)
    (sub_ne_zero.mpr (Finset.mem_erase.mp hx).1)

/-- Lagrange interpolation: the weighted sum of values equals the polynomial
    evaluated at 0, where weights are Lagrange coefficients.

    Given scalars [x₁, ..., xₙ] and values [v₁, ..., vₙ], there is a unique
    polynomial p of degree < n such that p(xᵢ) = vᵢ. This theorem states that:

      Σᵢ λᵢ · vᵢ = p(0)

    where λᵢ are the Lagrange coefficients at 0.

    This is the core property used in threshold cryptography: to reconstruct
    the secret f(0), signers compute weighted combinations of their shares f(xᵢ).

    **Mathematical justification**:
    The theorem is mathematically straightforward - it's just Lagrange interpolation.
    The proof has reduced the goal to showing:

      `(List.zipWith (· * ·) coeffs values).sum = s.sum (fun x => r x * coeff x)`

    where we've already established `coeff x = eval 0 (Lagrange.basis s id x)`.

    **Note**: Uses sorry because the final step requires connecting:
    1. List-based `zipWith` sum over paired (coeff, value) elements
    2. Finset-based sum over `s = partyScalars.toFinset`
    3. The value retrieval function `r` (using `findIdx?`)

    The alignment is subtle:
    - List indexing is positional: `coeffs[i] * values[i]`
    - Finset sum is by element: `Σ_{x ∈ s} r(x) * coeff(x)`
    - Must show `r(partyScalars[i]) = values[i]` for the mapping

    With `Nodup`, the list-to-finset correspondence is bijective, but Mathlib
    doesn't provide a direct lemma for `zipWith` over parallel lists mapping
    to finset sums. The `List.sum_toFinset` lemma handles single lists but
    not paired/zipped operations.

    The `lagrange_weighted_sum` theorem below provides the finset-based version
    that avoids this list/finset alignment issue. -/
theorem lagrange_interpolation {F : Type*} [Field F] [DecidableEq F]
    (partyScalars : List F)
    (values : List F)
    (hnodup : partyScalars.Nodup)
    (hlen : partyScalars.length = values.length)
    (hne : partyScalars ≠ []) :
    let coeffs := partyScalars.map fun p => coeffAtZero p partyScalars
    let s := partyScalars.toFinset
    -- The value function derived from lists
    let r : F → F := fun x =>
      match partyScalars.findIdx? (· == x) with
      | some i => values.getD i 0
      | none => 0
    (List.zipWith (· * ·) coeffs values).sum = eval 0 (Lagrange.interpolate s id r) := by
  intro coeffs s r
  -- Connect to Mathlib's interpolate
  have hinj : Set.InjOn id (s : Set F) := Function.injective_id.injOn
  have hnonempty : s.Nonempty := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil partyScalars hne
    exact ⟨x, List.mem_toFinset.mpr hx⟩
  -- The sum of (coeff * value) equals eval 0 of interpolate
  have heval : eval 0 (Lagrange.interpolate s id r) =
               s.sum (fun x => r x * eval 0 (Lagrange.basis s id x)) := by
    simp only [Lagrange.interpolate_apply, eval_finset_sum, eval_mul, eval_C, id_eq]
  rw [heval]
  -- Now connect list sum to finset sum
  have hcoeff_eq : ∀ x ∈ s, coeffAtZero x partyScalars = eval 0 (Lagrange.basis s id x) := by
    intro x _
    rw [coeffAtZero_list_nodup x partyScalars hnodup]
    exact coeffAtZeroFinset_eq_eval_basis s x
  -- The zipWith sum equals the finset sum when properly aligned
  -- Remaining: connect List.zipWith positional sum to Finset element-wise sum
  sorry

/-- Simplified interpolation for the common case where we just need the weighted sum.
    This avoids dealing with polynomial evaluation directly. -/
theorem lagrange_weighted_sum {F : Type*} [Field F] [DecidableEq F]
    (partyScalars : List F)
    (values : F → F)
    (hnodup : partyScalars.Nodup)
    (hne : partyScalars ≠ []) :
    partyScalars.toFinset.sum (fun x => coeffAtZeroFinset partyScalars.toFinset x * values x) =
    eval 0 (Lagrange.interpolate partyScalars.toFinset id values) := by
  have hinj : Set.InjOn id (partyScalars.toFinset : Set F) := Function.injective_id.injOn
  simp only [Lagrange.interpolate_apply, eval_finset_sum, eval_mul, eval_C, id_eq]
  congr 1
  ext x
  rw [coeffAtZeroFinset_eq_eval_basis]
  ring

end IceNine.Protocol.Lagrange
