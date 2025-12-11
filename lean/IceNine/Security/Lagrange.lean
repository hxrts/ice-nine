/-
# Lagrange-Weighted Correctness

Correctness proofs for t-of-n threshold signing using Lagrange interpolation.
Instead of simple sum z = Σ z_i, we weight by Lagrange coefficients:
  z = Σ λ_i · z_i

Key property: if shares lie on a degree-(t-1) polynomial, Lagrange
coefficients reconstruct the polynomial value at 0 (the secret).

## Mathlib Integration

We connect our `lagrangeCoeffAtZero` to Mathlib's `Lagrange.basis` polynomial.
Our coefficient λ_i = Π_{j≠i} x_j/(x_j - x_i) is exactly `(Lagrange.basis s v i).eval 0`.

Mathlib provides:
- `Lagrange.basis`: Basis polynomial evaluating to 1 at node i, 0 at others
- `Lagrange.sum_basis`: Σ_i basis_i = 1 (partition of unity)
- `Lagrange.eval_interpolate_at_node`: Interpolant evaluates correctly at nodes

**Reference**: Mathlib.LinearAlgebra.Lagrange
-/

import Mathlib
import IceNine.Protocol.Sign.Sign
import IceNine.Instances

namespace IceNine.Security

open IceNine.Protocol
open IceNine.Instances
open Polynomial

/-!
## Lagrange Linearity

Core algebraic lemma: weighted partial signatures aggregate correctly.
Σ λ_i·(y_i + c·sk_i) = Σλ_i·y_i + c·Σλ_i·sk_i
-/

/-- Lagrange-weighted aggregation splits linearly (integer version).
    Σ λ_i·(y_i + c·sk_i) = Σλ_i·y_i + c·Σλ_i·sk_i. -/
lemma sum_zipWith_scaled_add_mul (c : Int) :
  ∀ (ys sks coeffs : List Int),
    (List.zipWith3 (fun λ y s => λ * y + λ * (c * s)) coeffs ys sks).sum
      = (coeffs.zipWith (·*·) ys).sum + c * (coeffs.zipWith (·*·) sks).sum
  | [], [], [] => by simp
  | [], _, _ => by simp
  | _, [], _ => by simp
  | _, _, [] => by simp
  | λ::λs, y::ys, s::sks =>
      have ih := sum_zipWith_scaled_add_mul ys sks λs
      simp [List.sum_cons, ih, mul_add, add_assoc, add_left_comm, add_comm, left_distrib, right_distrib, mul_comm, mul_left_comm]

/-!
## Threshold Correctness

Verify that Lagrange-weighted aggregation produces valid signatures.
pk and w are also Lagrange-weighted sums of the individual shares.
-/

/-- Happy-path correctness for t-of-n threshold signing.
    Uses Lagrange coefficients to weight partial signatures. -/
lemma verify_happy_simple_lagrange
    (ys sks coeffs : List Int)  -- nonces, secrets, Lagrange coefficients
    (m : ByteArray)
    (Sset : List Nat)
    (session fromId : Nat) :
  -- pk and w are Lagrange-weighted sums
  let pk : Int := (coeffs.zipWith (·*·) sks).sum  -- Σ λ_i·sk_i
  let w  : Int := (coeffs.zipWith (·*·) ys).sum   -- Σ λ_i·y_i
  let c  : Int := simpleScheme.hash m pk Sset [] w
  let coeffStructs : List (LagrangeCoeff simpleScheme) :=
    coeffs.map (fun λ => { pid := fromId, lambda := λ })
  let shares : List (SignShareMsg simpleScheme) :=
    List.zipWith (fun y s => { sender := fromId, session := session, z_i := y + c * s }) ys sks
  let sig : Signature simpleScheme :=
    aggregateSignatureLagrange simpleScheme c Sset [] coeffStructs shares
  verify simpleScheme pk m sig := by
  intros pk w c coeffStructs shares sig
  simp [aggregateSignatureLagrange, verify, simpleScheme, normOKAlways,
        smul_int_eq_mul, sum_zipWith_scaled_add_mul, LinearMap.id_apply, List.zipWith, List.zipWith3, List.foldl_map] at *
  ring_nf

/-!
## Connection to Mathlib Lagrange

We show that our `lagrangeCoeffAtZero` computes the same value as
`(Lagrange.basis s v i).eval 0` from Mathlib.

This connects our implementation to Mathlib's verified Lagrange theory,
giving us access to theorems like:
- `Lagrange.sum_basis`: Σ_i λ_i = 1 (when evaluating polynomial at 0)
- `Lagrange.eval_interpolate_at_node`: interpolation correctness
-/

/-- Our Lagrange coefficient equals Mathlib's basis polynomial evaluated at 0.

    lagrangeCoeffAtZero computes: Π_{j≠i} x_j / (x_j - x_i)

    Mathlib's Lagrange.basis s v i is the polynomial Π_{j≠i} (X - x_j) / (x_i - x_j)
    which evaluates at 0 to: Π_{j≠i} (0 - x_j) / (x_i - x_j) = Π_{j≠i} x_j / (x_j - x_i)

    This is exactly our formula. -/
theorem lagrangeCoeffAtZero_eq_basis_eval
    {F : Type*} [Field F] [DecidableEq F]
    (s : Finset F) (v : F → F) (i : F) (hi : i ∈ s)
    (hv : Set.InjOn v s) :
    (s.erase i).prod (fun j => v j / (v j - v i))
      = (Lagrange.basis s v i).eval 0 := by
  -- The basis polynomial is Π_{j∈s, j≠i} (X - v j) / (v i - v j)
  -- At X = 0: Π_{j≠i} (- v j) / (v i - v j) = Π_{j≠i} (v j) / (v j - v i)
  simp only [Lagrange.basis, Lagrange.basisDivisor]
  rw [Finset.prod_congr rfl]
  intro j hj
  simp only [eval_mul, eval_C, eval_sub, eval_X]
  rw [Finset.mem_erase] at hj
  have hne : v i ≠ v j := by
    intro heq
    have : i = j := hv hi (Finset.mem_of_mem_erase hj) heq
    exact hj.1 this
  field_simp
  ring

/-- Lagrange coefficients sum to 1 when evaluating at a point in the interpolation set.

    This follows from Mathlib's Lagrange.sum_basis which shows:
    Σ_{i∈s} (Lagrange.basis s v i) = 1 (as polynomials)

    Evaluating at 0: Σ_{i∈s} λ_i = 1 -/
theorem lagrangeCoeffs_sum_one
    {F : Type*} [Field F] [DecidableEq F]
    (s : Finset F) (v : F → F)
    (hs : s.Nonempty) (hv : Set.InjOn v s) :
    s.sum (fun i => (Lagrange.basis s v i).eval 0) = 1 := by
  have := Lagrange.sum_basis v hs hv
  calc s.sum (fun i => (Lagrange.basis s v i).eval 0)
      = (s.sum (fun i => Lagrange.basis s v i)).eval 0 := by rw [eval_finset_sum]
    _ = (1 : F[X]).eval 0 := by rw [this]
    _ = 1 := eval_one

/-- Main interpolation theorem: Lagrange-weighted sum recovers function value.

    If shares are values of a polynomial p at nodes v(i), then
    Σ λ_i · p(v(i)) = p(0)

    This is the core property ensuring threshold signing reconstructs correctly. -/
theorem lagrange_interpolation_at_zero
    {F : Type*} [Field F] [DecidableEq F]
    (s : Finset F) (v : F → F) (r : F → F)
    (hs : s.Nonempty) (hv : Set.InjOn v s)
    (p : F[X]) (hp : p.degree < s.card)
    (hr : ∀ i ∈ s, p.eval (v i) = r i) :
    s.sum (fun i => (Lagrange.basis s v i).eval 0 * r i) = p.eval 0 := by
  -- Use Mathlib's interpolation theorem
  have heq : p = Lagrange.interpolate s v r := by
    rw [Lagrange.eq_interpolate_iff hs hv]
    exact ⟨hp, hr⟩
  calc s.sum (fun i => (Lagrange.basis s v i).eval 0 * r i)
      = (Lagrange.interpolate s v r).eval 0 := by
        simp only [Lagrange.interpolate, eval_finset_sum, eval_mul, eval_C]
    _ = p.eval 0 := by rw [← heq]

end IceNine.Security
