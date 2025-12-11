/-
# List Lemmas for zipWith and sum

Reusable algebraic lemmas about List.zipWith and List.sum.
These lemmas support correctness proofs for signature aggregation,
share refresh, and repair protocols.

**Mathlib Note**: These lemmas don't have direct equivalents in Mathlib.
The closest are `List.sum_map_add` for mapped addition and various
`zipWith` lemmas, but not the specific combination needed here.
-/

import Mathlib

namespace List

/-!
## Sum of zipWith (· + ·)

Core lemma: Σ(a_i + b_i) = Σa_i + Σb_i (when lengths match).
-/

/-- Sum of zipWith add distributes over truncated lists.
    Handles the general case where list lengths may differ. -/
theorem sum_zipWith_add {α : Type*} [AddCommMonoid α] :
    ∀ (as bs : List α),
      (zipWith (· + ·) as bs).sum = as.take bs.length |>.sum + bs.take as.length |>.sum
  | [], _ => by simp
  | _, [] => by simp
  | a::as, b::bs => by
      simp only [zipWith_cons_cons, sum_cons, take_succ_cons, length_cons]
      rw [sum_zipWith_add as bs]
      ring

/-- When lists have equal length, take is identity. -/
theorem take_eq_self_of_length_eq {α : Type*} (as bs : List α) (h : as.length = bs.length) :
    as.take bs.length = as := by
  simp [take_length_le, h]

/-- Sum of zipWith add for equal-length lists.
    Σ(a_i + b_i) = Σa_i + Σb_i -/
theorem sum_zipWith_add_eq {α : Type*} [AddCommMonoid α]
    (as bs : List α) (h : as.length = bs.length) :
    (zipWith (· + ·) as bs).sum = as.sum + bs.sum := by
  rw [sum_zipWith_add]
  rw [take_eq_self_of_length_eq as bs h]
  rw [take_eq_self_of_length_eq bs as h.symm]

/-!
## Sum of zipWith with scalar multiplication

For signature aggregation: Σ(y_i + c·s_i) = Σy_i + c·Σs_i
-/

/-- Sum distributes over zipWith with addition and scalar multiplication (Int version).
    Σ(y_i + c·s_i) = Σy_i + c·Σs_i -/
lemma sum_zipWith_add_mul (c : Int) (ys sks : List Int) :
    (zipWith (fun y s => y + c * s) ys sks).sum = ys.sum + c * sks.sum := by
  induction ys generalizing sks with
  | nil => simp
  | cons y ys ih =>
    cases sks with
    | nil => simp
    | cons s sks =>
      simp only [zipWith_cons_cons, sum_cons]
      rw [ih sks]
      ring

/-- Sum distributes over zipWith with addition and scalar multiplication (module version).
    Σ(y_i + c•s_i) = Σy_i + c•Σs_i

    Uses `smul_add` from Mathlib module theory. -/
lemma sum_zipWith_add_smul
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (c : R) (ys sks : List M) :
    (zipWith (fun y s => y + c • s) ys sks).sum = ys.sum + c • sks.sum := by
  induction ys generalizing sks with
  | nil => simp
  | cons y ys ih =>
    cases sks with
    | nil => simp
    | cons s sks =>
      simp only [zipWith_cons_cons, sum_cons, smul_add]
      rw [ih sks]
      abel

/-!
## Sum of zipWith3 with Lagrange coefficients

For threshold signing: Σ λ_i·(y_i + c·s_i) = Σλ_i·y_i + c·Σλ_i·s_i
-/

/-- Lagrange-weighted aggregation splits linearly.
    Σ λ_i·(y_i + c·s_i) = Σλ_i·y_i + c·Σλ_i·s_i -/
lemma sum_zipWith3_scaled_add_mul (c : Int) (ys sks coeffs : List Int) :
    (zipWith3 (fun λ y s => λ * y + λ * (c * s)) coeffs ys sks).sum
      = (coeffs.zipWith (·*·) ys).sum + c * (coeffs.zipWith (·*·) sks).sum := by
  induction coeffs generalizing ys sks with
  | nil => simp
  | cons λ λs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      cases sks with
      | nil => simp
      | cons s sks =>
        simp only [zipWith3_cons_cons_cons, zipWith_cons_cons, sum_cons]
        rw [ih ys sks]
        ring

end List
