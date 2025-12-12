/-
# Lagrange Interpolation Proofs

Correctness proofs for Lagrange interpolation coefficients used in
threshold cryptography.

## Key Theorems

1. `coeffAtZeroFinset_eq_eval_basis`: Our coefficient = Mathlib's basis at 0
2. `coeffAtZero_list_nodup`: List and finset formulations coincide
3. `coeffAtZeroFinset_sum_one`: Coefficients sum to 1 (partition of unity)
4. `coeffs_sum_to_one`: List-based sum-to-one
5. `coeff_zero_not_in`: Coefficient for element not in set
6. `coeff_nonzero_in_set`: Coefficients are nonzero for valid sets
7. `lagrange_interpolation`: List-based interpolation theorem
8. `lagrange_weighted_sum`: Finset-based weighted sum theorem

## Mathlib Integration

We connect our `coeffAtZero` to Mathlib's `Lagrange.basis` polynomial.
Our coefficient λ_i = Π_{j≠i} x_j/(x_j - x_i) is exactly `(Lagrange.basis s id i).eval 0`.

**Reference**: Mathlib.LinearAlgebra.Lagrange
-/

import Mathlib
import IceNine.Protocol.Core.Lagrange

namespace IceNine.Proofs.Lagrange

open IceNine.Protocol.Lagrange
open Polynomial Lagrange Finset

/-!
## Connection to Mathlib

These theorems establish the equivalence between our Lagrange coefficient
implementation and Mathlib's verified Lagrange interpolation theory.
-/

/-- Our coefficient matches the evaluation of Mathlib's Lagrange basis at 0.
    This is the key connection to Mathlib's Lagrange interpolation theory.

    **Mathematical justification**:
    Our definition: `coeffAtZeroFinset s x = ∏ xj ∈ s.erase x, (xj / (xj - x))`

    Mathlib's basis uses `basisDivisor`:
      basis s v i = ∏ j ∈ s.erase i, basisDivisor (v i) (v j)
      basisDivisor a b = C ((a - b)⁻¹) * (X - C b)

    Evaluating basis at 0 with v = id:
      eval 0 (basis s id x) = ∏ j ∈ s.erase x, eval 0 (basisDivisor x j)
                            = ∏ j ∈ s.erase x, (x - j)⁻¹ * (0 - j)
                            = ∏ j ∈ s.erase x, j / (j - x)

    This matches our definition exactly. -/
theorem coeffAtZeroFinset_eq_eval_basis {F : Type*} [Field F] [DecidableEq F]
    (s : Finset F) (x : F) :
    coeffAtZeroFinset s x = eval 0 (Lagrange.basis s id x) := by
  simp only [coeffAtZeroFinset, Lagrange.basis, id_eq]
  rw [eval_prod]
  congr 1
  ext j
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  rw [div_eq_mul_inv]
  rw [show (j - x)⁻¹ = -((x - j)⁻¹) by rw [← neg_sub x j, neg_inv]]
  ring

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
  have heq : ∀ x ∈ s, coeffAtZeroFinset s x = eval 0 (Lagrange.basis s id x) := fun x _ =>
    coeffAtZeroFinset_eq_eval_basis s x
  calc s.sum (fun x => coeffAtZeroFinset s x)
      = s.sum (fun x => eval 0 (Lagrange.basis s id x)) := sum_congr rfl heq
    _ = eval 0 (s.sum (fun x => Lagrange.basis s id x)) := (eval_finset_sum s _ 0).symm
    _ = eval 0 1 := by
        have hinj : Set.InjOn id (s : Set F) := Function.injective_id.injOn
        have hsum : (∑ j ∈ s, Lagrange.basis s id j) = (1 : F[X]) := by
          simpa using Lagrange.sum_basis (s := s) (v := id) hinj h
        simpa [hsum]
    _ = 1 := eval_one

/-!
## List-Based Theorems

These theorems work with list representations, which are more convenient
for protocol implementations.
-/

/-- The sum of all Lagrange coefficients equals 1.
    This is the list-based version of coeffAtZeroFinset_sum_one. -/
theorem coeffs_sum_to_one {F : Type*} [Field F] [DecidableEq F]
    (partyScalars : List F)
    (hnodup : partyScalars.Nodup)
    (hne : partyScalars ≠ []) :
    ((allCoeffsAtZero partyScalars).map Prod.snd).sum = 1 := by
  have hnonempty : partyScalars.toFinset.Nonempty := by
    obtain ⟨x, hx⟩ : ∃ x, x ∈ partyScalars := List.exists_mem_of_ne_nil partyScalars hne
    exact ⟨x, List.mem_toFinset.mpr hx⟩
  have hco : (allCoeffsAtZero partyScalars).map Prod.snd =
              partyScalars.map (fun p => coeffAtZeroFinset partyScalars.toFinset p) := by
    simp only [allCoeffsAtZero, List.map_map, Function.comp]
    congr 1; ext p
    exact coeffAtZero_list_nodup p partyScalars hnodup
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
  have hmem : partyScalar ∉ allScalars.toFinset := List.mem_toFinset.not.mpr hnotin
  simp only [coeffAtZero, hnodup, if_true, Finset.erase_eq_of_notMem hmem]
  classical
  let f : F → F := fun xj => xj / (xj - partyScalar)
  have hprod : (∏ xj ∈ allScalars.toFinset, f xj) = (allScalars.map f).prod := by
    simpa using (List.prod_toFinset (l := allScalars) (f := f) hnodup)
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
  rw [coeffAtZero_list_nodup _ _ hnodup, coeffAtZeroFinset]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro x hx
  exact div_ne_zero
    (hnozero x (List.mem_toFinset.mp (Finset.mem_erase.mp hx).2) (Finset.mem_erase.mp hx).1)
    (sub_ne_zero.mpr (Finset.mem_erase.mp hx).1)

/-!
## Interpolation Theorems

These theorems establish that Lagrange-weighted sums correctly reconstruct
polynomial values at 0 - the core property for threshold cryptography.
-/

/-- Helper: zipWith sum over a Nodup list equals finset sum.
    This connects list-based positional operations to finset element-wise operations. -/
lemma zipWith_mul_sum_eq_finset_sum {F : Type*} [Field F] [DecidableEq F]
    (partyScalars : List F)
    (values : List F)
    (f : F → F)
    (hnodup : partyScalars.Nodup)
    (hlen : partyScalars.length = values.length) :
    (List.zipWith (fun p v => f p * v) partyScalars values).sum =
    partyScalars.toFinset.sum (fun x =>
      f x * (values.getD (partyScalars.indexOf x) 0)) := by
  induction partyScalars generalizing values with
  | nil => simp
  | cons p ps ih =>
    match values with
    | [] => simp at hlen
    | v :: vs =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      have hnodup' : ps.Nodup := List.Nodup.of_cons hnodup
      have hlen' : ps.length = vs.length := by simp only [List.length_cons] at hlen; omega
      have hnotmem : p ∉ ps := List.not_mem_of_nodup_cons hnodup
      rw [ih vs hnodup' hlen']
      -- Split the finset sum: {p} ∪ ps.toFinset
      have hdisjoint : Disjoint ({p} : Finset F) ps.toFinset := by
        simp only [Finset.disjoint_singleton_left, List.mem_toFinset]
        exact hnotmem
      have hunion : (p :: ps).toFinset = {p} ∪ ps.toFinset := by
        ext x
        simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_union,
                   Finset.mem_singleton, List.mem_toFinset]
      rw [hunion, Finset.sum_union hdisjoint]
      simp only [Finset.sum_singleton]
      congr 1
      · -- The p term: indexOf p in (p::ps) = 0, so getD 0 = v
        simp only [List.indexOf_cons_self, List.getD_cons_zero]
      · -- The ps terms: indexOf x in (p::ps) = 1 + indexOf x in ps
        apply Finset.sum_congr rfl
        intro x hx
        have hxne : x ≠ p := by
          intro heq
          rw [heq] at hx
          exact hnotmem (List.mem_toFinset.mp hx)
        simp only [List.indexOf_cons_ne _ hxne, List.getD_cons_succ]

/-- Lagrange interpolation: the weighted sum of values equals the polynomial
    evaluated at 0, where weights are Lagrange coefficients.

    Given scalars [x₁, ..., xₙ] and values [v₁, ..., vₙ], there is a unique
    polynomial p of degree < n such that p(xᵢ) = vᵢ. This theorem states that:

      Σᵢ λᵢ · vᵢ = p(0)

    where λᵢ are the Lagrange coefficients at 0.

    This is the core property used in threshold cryptography: to reconstruct
    the secret f(0), signers compute weighted combinations of their shares f(xᵢ).

    The proof connects list-based zipWith sum to finset element-wise sum by
    showing that for Nodup lists, summing over list positions is equivalent
    to summing over the corresponding finset elements. -/
theorem lagrange_interpolation {F : Type*} [Field F] [DecidableEq F]
    (partyScalars : List F)
    (values : List F)
    (hnodup : partyScalars.Nodup)
    (hlen : partyScalars.length = values.length)
    (hne : partyScalars ≠ []) :
    let coeffs := partyScalars.map fun p => coeffAtZero p partyScalars
    let s := partyScalars.toFinset
    let r : F → F := fun x =>
      match partyScalars.findIdx? (· == x) with
      | some i => values.getD i 0
      | none => 0
    (List.zipWith (· * ·) coeffs values).sum = eval 0 (Lagrange.interpolate s id r) := by
  intro coeffs s r
  have _hinj : Set.InjOn id (s : Set F) := Function.injective_id.injOn
  have _hnonempty : s.Nonempty := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil partyScalars hne
    exact ⟨x, List.mem_toFinset.mpr hx⟩
  -- Evaluate the interpolation polynomial at 0
  have heval : eval 0 (Lagrange.interpolate s id r) =
               s.sum (fun x => r x * eval 0 (Lagrange.basis s id x)) := by
    simp only [Lagrange.interpolate_apply, eval_finset_sum, eval_mul, eval_C, id_eq]
  rw [heval]
  -- Connect coefficients to basis evaluation
  have hcoeff_eq : ∀ x ∈ s, coeffAtZero x partyScalars = eval 0 (Lagrange.basis s id x) := by
    intro x _
    rw [coeffAtZero_list_nodup x partyScalars hnodup]
    exact coeffAtZeroFinset_eq_eval_basis s x
  -- Rewrite LHS using zipWith_map_left
  have hzipWith_eq : (List.zipWith (· * ·) coeffs values).sum =
      (List.zipWith (fun p v => coeffAtZero p partyScalars * v) partyScalars values).sum := by
    congr 1
    rw [List.zipWith_map_left]
  rw [hzipWith_eq]
  -- Apply the helper lemma
  rw [zipWith_mul_sum_eq_finset_sum partyScalars values (fun p => coeffAtZero p partyScalars) hnodup hlen]
  -- Show the finset sums are equal
  apply Finset.sum_congr rfl
  intro x hx
  -- For x ∈ s, show: coeffAtZero x * getD (indexOf x) = r x * basis eval
  have hxmem : x ∈ partyScalars := List.mem_toFinset.mp hx
  -- r x = values.getD (indexOf x) 0 for x ∈ partyScalars
  have hr : r x = values.getD (partyScalars.indexOf x) 0 := by
    simp only [r]
    have hfind : partyScalars.findIdx? (· == x) = some (partyScalars.indexOf x) := by
      rw [List.findIdx?_eq_some_iff]
      have hidx := List.indexOf_lt_length.mpr hxmem
      constructor
      · exact hidx
      constructor
      · simp only [beq_iff_eq, List.getElem_indexOf]
      · intro k hk
        simp only [beq_iff_eq, not_true_eq_false, imp_false, Decidable.not_not]
        intro hpk
        have : partyScalars[k] = partyScalars[partyScalars.indexOf x] := by
          rw [hpk, List.getElem_indexOf]
        exact List.Nodup.getElem_eq_iff hnodup hk hidx |>.mp this
    rw [hfind]
  rw [hr, hcoeff_eq x hx]
  ring

/-- Simplified interpolation for the common case where we just need the weighted sum.
    This avoids dealing with polynomial evaluation directly and works with finsets. -/
theorem lagrange_weighted_sum {F : Type*} [Field F] [DecidableEq F]
    (partyScalars : List F)
    (values : F → F)
    (_hnodup : partyScalars.Nodup)
    (_hne : partyScalars ≠ []) :
    partyScalars.toFinset.sum (fun x => coeffAtZeroFinset partyScalars.toFinset x * values x) =
    eval 0 (Lagrange.interpolate partyScalars.toFinset id values) := by
  have hinj : Set.InjOn id (partyScalars.toFinset : Set F) := Function.injective_id.injOn
  simp only [Lagrange.interpolate_apply, eval_finset_sum, eval_mul, eval_C, id_eq]
  congr 1
  ext x
  rw [coeffAtZeroFinset_eq_eval_basis]
  ring

end IceNine.Proofs.Lagrange
