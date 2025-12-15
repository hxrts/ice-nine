/-
# Norm Properties

Lemmas about norm behavior for List Int vectors. These properties are useful
for reasoning about norm bounds in threshold signing.

Separated from Protocol/Core/NormBounded.lean to maintain protocol/proof separation.
-/

import IceNine.Protocol.Core.NormBounded
import Mathlib

set_option autoImplicit false

namespace IceNine.Proofs.Core.NormProperties

-- Open NormBounded namespace for norm function and typeclass
open IceNine.Protocol.NormBounded

/-- Alias for NormBounded.norm to avoid ambiguity with Mathlib's Norm.norm -/
abbrev infNorm {α : Type*} [NormBounded α] : α → Nat := NormBounded.norm

/-!
## Basic Properties
-/

/-- Norm of empty list is 0 -/
theorem norm_nil : infNorm ([] : List Int) = 0 := rfl

/-- Helper: foldl max is monotonic in init -/
private theorem foldl_max_mono (l : List Int) (a b : Nat) (hab : a ≤ b) :
    l.foldl (fun acc x => max acc (Int.natAbs x)) a ≤ l.foldl (fun acc x => max acc (Int.natAbs x)) b := by
  induction l generalizing a b with
  | nil => exact hab
  | cons x xs ih =>
    simp only [List.foldl]
    apply ih
    omega

/-- Helper: foldl max is at least init -/
private theorem foldl_max_ge_init (l : List Int) (init : Nat) :
    init ≤ l.foldl (fun acc x => max acc (Int.natAbs x)) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl init
  | cons x xs ih =>
    simp only [List.foldl]
    exact Nat.le_trans (Nat.le_max_left init _) (ih _)

/-- Norm is monotonic under list membership -/
theorem norm_mem_le (v : List Int) (x : Int) (hx : x ∈ v) :
    Int.natAbs x ≤ infNorm v := by
  induction v with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [infNorm, NormBounded.norm, List.foldl]
    cases List.mem_cons.mp hx with
    | inl heq =>
      rw [heq]
      have h1 : Int.natAbs y ≤ max 0 (Int.natAbs y) := Nat.le_max_right 0 _
      exact Nat.le_trans h1 (foldl_max_ge_init ys (max 0 (Int.natAbs y)))
    | inr hmem =>
      have h1 := ih hmem
      exact Nat.le_trans h1 (foldl_max_mono ys 0 (max 0 (Int.natAbs y)) (Nat.le_max_left _ _))

/-!
## Triangle Inequality
-/

/-- Helper: norm of cons is at least norm of tail -/
private theorem norm_cons_ge (l : List Int) (x : Int) : infNorm l ≤ infNorm (x :: l) := by
  unfold infNorm NormBounded.norm
  exact foldl_max_mono l 0 (max 0 (Int.natAbs x)) (Nat.zero_le _)

/-- Helper: foldl max is bounded if init and all elements are bounded -/
private theorem foldl_max_le_bound' (l : List Int) (bound : Nat) (init : Nat)
    (hinit : init ≤ bound) (helem : ∀ z ∈ l, Int.natAbs z ≤ bound) :
    l.foldl (fun acc x => max acc (Int.natAbs x)) init ≤ bound := by
  induction l generalizing init with
  | nil => exact hinit
  | cons x xs ih =>
    simp only [List.foldl]
    have hx := helem x List.mem_cons_self
    have hxs : ∀ z ∈ xs, Int.natAbs z ≤ bound := fun z hz => helem z (List.mem_cons_of_mem x hz)
    have hmax : max init (Int.natAbs x) ≤ bound := Nat.max_le.mpr ⟨hinit, hx⟩
    exact ih (max init (Int.natAbs x)) hmax hxs

/-- Triangle inequality for list norm under zipWith addition.
    Uses the fact that max |v_i + w_i| ≤ max |v_i| + max |w_i| by pointwise triangle inequality. -/
theorem norm_add_le (v w : List Int) (hlen : v.length = w.length) :
    infNorm (List.zipWith (· + ·) v w) ≤ infNorm v + infNorm w := by
  -- Every element of the result is bounded by corresponding elements
  have hbound : ∀ z ∈ List.zipWith (· + ·) v w, Int.natAbs z ≤ infNorm v + infNorm w := by
    intro z hz
    induction v generalizing w with
    | nil => simp at hz
    | cons a as ih =>
      match w with
      | [] => simp at hz
      | b :: bs =>
        simp only [List.zipWith_cons_cons, List.mem_cons] at hz
        rcases hz with heq | hmem
        · rw [heq]
          have h1 : Int.natAbs (a + b) ≤ Int.natAbs a + Int.natAbs b := Int.natAbs_add_le a b
          have h2 : Int.natAbs a ≤ infNorm (a :: as) := norm_mem_le (a :: as) a List.mem_cons_self
          have h3 : Int.natAbs b ≤ infNorm (b :: bs) := norm_mem_le (b :: bs) b List.mem_cons_self
          omega
        · have hlen' : as.length = bs.length := by simp at hlen; exact hlen
          have h1 := ih bs hlen' hmem
          have h2 : infNorm as ≤ infNorm (a :: as) := norm_cons_ge as a
          have h3 : infNorm bs ≤ infNorm (b :: bs) := norm_cons_ge bs b
          omega
  -- Now show norm of result ≤ this bound using the fold bound lemma
  unfold infNorm NormBounded.norm
  have hinit : (0 : Nat) ≤ infNorm v + infNorm w := Nat.zero_le _
  exact foldl_max_le_bound' (l := List.zipWith (· + ·) v w)
      (bound := infNorm v + infNorm w) (init := 0) hinit hbound

/-!
## Scaling Property
-/

/-- Scaling bound: ‖c·v‖∞ ≤ |c| · ‖v‖∞.
    Actually an equality: max |c * x_i| = |c| * max |x_i|. -/
theorem norm_smul_le (c : Int) (v : List Int) :
    infNorm (v.map (c * ·)) ≤ Int.natAbs c * infNorm v := by
  -- Bound every coefficient of the scaled list by |c| * ‖v‖∞, then apply `foldl_max_le_bound'`.
  unfold infNorm NormBounded.norm
  let base := v.foldl (fun acc x => max acc (Int.natAbs x)) 0
  have hbase : base = v.foldl (fun acc x => max acc (Int.natAbs x)) 0 := rfl
  -- Every element of the scaled list is within the bound
  have helem : ∀ z ∈ v.map (c * ·), Int.natAbs z ≤ Int.natAbs c * base := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
    have hx_le : Int.natAbs x ≤ base := by
      -- reuse `norm_mem_le` on the original list
      simpa [infNorm, NormBounded.norm, hbase] using (norm_mem_le v x hx)
    calc
      Int.natAbs (c * x) = Int.natAbs c * Int.natAbs x := Int.natAbs_mul _ _
      _ ≤ Int.natAbs c * base := Nat.mul_le_mul_left _ hx_le
  -- Apply fold bound with init = 0
  have hinit : (0 : Nat) ≤ Int.natAbs c * base := Nat.zero_le _
  have h := foldl_max_le_bound' (l := v.map (c * ·))
      (bound := Int.natAbs c * base) (init := 0) hinit helem
  simpa [infNorm, NormBounded.norm, hbase] using h

end IceNine.Proofs.Core.NormProperties
