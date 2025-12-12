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

set_option autoImplicit false

namespace List

/-!
## Sum of zipWith (· + ·)

Core lemma: Σ(a_i + b_i) = Σa_i + Σb_i (when lengths match).
-/

/-- Sum of zipWith add distributes over truncated lists.
    Handles the general case where list lengths may differ. -/
theorem sum_zipWith_add {α : Type*} [AddCommMonoid α] :
    ∀ (as bs : List α),
      (zipWith (· + ·) as bs).sum = (List.take bs.length as).sum + (List.take as.length bs).sum
  | [], _ => by simp
  | _, [] => by simp
  | a::as, b::bs => by
      simp only [zipWith_cons_cons, sum_cons, List.take_succ_cons, length_cons]
      rw [sum_zipWith_add as bs]
      abel

/-- When lists have equal length, take is identity. -/
theorem take_eq_self_of_length_eq {α : Type*} (as bs : List α) (h : as.length = bs.length) :
    List.take bs.length as = as := by
  rw [← h]
  simp only [List.take_length]

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
    Σ(y_i + c·s_i) = Σy_i + c·Σs_i
    Requires equal-length lists since zipWith truncates. -/
lemma sum_zipWith_add_mul (c : Int) (ys sks : List Int) (hlen : ys.length = sks.length) :
    (zipWith (fun y s => y + c * s) ys sks).sum = ys.sum + c * sks.sum := by
  induction ys generalizing sks with
  | nil =>
    match sks with
    | [] => simp
    | _::_ => simp only [length_nil, length_cons] at hlen; omega
  | cons y ys ih =>
    match sks with
    | [] => simp only [length_nil, length_cons] at hlen; omega
    | s::sks' =>
      simp only [length_cons, add_left_inj] at hlen
      simp only [zipWith_cons_cons, sum_cons]
      rw [ih sks' hlen]
      ring

/-- Sum distributes over zipWith with addition and scalar multiplication (module version).
    Σ(y_i + c•s_i) = Σy_i + c•Σs_i
    Requires equal-length lists since zipWith truncates.

    Uses `smul_add` from Mathlib module theory. -/
lemma sum_zipWith_add_smul
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (c : R) (ys sks : List M) (hlen : ys.length = sks.length) :
    (zipWith (fun y s => y + c • s) ys sks).sum = ys.sum + c • sks.sum := by
  induction ys generalizing sks with
  | nil =>
    match sks with
    | [] => simp
    | _::_ => simp only [length_nil, length_cons] at hlen; omega
  | cons y ys ih =>
    match sks with
    | [] => simp only [length_nil, length_cons] at hlen; omega
    | s::sks' =>
      simp only [length_cons, add_left_inj] at hlen
      simp only [zipWith_cons_cons, sum_cons, smul_add]
      rw [ih sks' hlen]
      abel

/-!
## Sum of zipWith3 with Lagrange coefficients

For threshold signing: Σ λ_i·(y_i + c·s_i) = Σλ_i·y_i + c·Σλ_i·s_i
-/

/-- Lagrange-weighted aggregation splits linearly.
    Σ λ_i·(y_i + c·s_i) = Σλ_i·y_i + c·Σλ_i·s_i
    Requires equal-length lists since zipWith3 truncates. -/
lemma sum_zipWith3_scaled_add_mul (c : Int) (ys sks coeffs : List Int)
    (hlen1 : coeffs.length = ys.length) (hlen2 : ys.length = sks.length) :
    (zipWith3 (fun coeff y s => coeff * y + coeff * (c * s)) coeffs ys sks).sum
      = (coeffs.zipWith (fun a b => a * b) ys).sum + c * (coeffs.zipWith (fun a b => a * b) sks).sum := by
  induction coeffs generalizing ys sks with
  | nil =>
    -- coeffs = [] implies ys = [] by hlen1, and sks = [] by hlen2
    match ys with
    | [] =>
      match sks with
      | [] => simp
      | _::_ => simp only [length_nil, length_cons] at hlen2; omega
    | _::_ => simp only [length_nil, length_cons] at hlen1; omega
  | cons coeff coeffs' ih =>
    match ys with
    | [] => simp only [length_nil, length_cons] at hlen1; omega
    | y::ys' =>
      match sks with
      | [] => simp only [length_nil, length_cons] at hlen2; omega
      | s::sks' =>
        simp only [length_cons, add_left_inj] at hlen1 hlen2
        simp only [zipWith3, zipWith_cons_cons, sum_cons]
        rw [ih ys' sks' hlen1 hlen2]
        ring

end List
