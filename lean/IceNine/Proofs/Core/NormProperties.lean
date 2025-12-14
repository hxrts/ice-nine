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
    have hx := helem x (List.mem_cons_self x xs)
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
          have h2 : Int.natAbs a ≤ infNorm (a :: as) := norm_mem_le (a :: as) a (List.mem_cons_self a as)
          have h3 : Int.natAbs b ≤ infNorm (b :: bs) := norm_mem_le (b :: bs) b (List.mem_cons_self b bs)
          omega
        · have hlen' : as.length = bs.length := by simp at hlen; exact hlen
          have h1 := ih bs hlen' hmem
          have h2 : infNorm as ≤ infNorm (a :: as) := norm_cons_ge as a
          have h3 : infNorm bs ≤ infNorm (b :: bs) := norm_cons_ge bs b
          omega
  -- Now show norm of result ≤ this bound
  unfold infNorm NormBounded.norm
  induction (List.zipWith (· + ·) v w) with
  | nil => exact Nat.zero_le _
  | cons x xs _ih =>
    have hx := hbound x (List.mem_cons_self x xs)
    have hxs : ∀ z ∈ xs, Int.natAbs z ≤ infNorm v + infNorm w := by
      intro z hz
      exact hbound z (List.mem_cons_of_mem x hz)
    have h1 : max 0 (Int.natAbs x) ≤ infNorm v + infNorm w := by omega
    exact foldl_max_le_bound' xs (infNorm v + infNorm w) (max 0 (Int.natAbs x)) h1 hxs

/-!
## Scaling Property
-/

/-- Scaling bound: ‖c·v‖∞ ≤ |c| · ‖v‖∞.
    Actually an equality: max |c * x_i| = |c| * max |x_i|. -/
theorem norm_smul_le (c : Int) (v : List Int) :
    infNorm (v.map (c * ·)) ≤ Int.natAbs c * infNorm v := by
  -- Use induction and the fact that |c * x| = |c| * |x|
  unfold infNorm NormBounded.norm
  induction v with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl, Int.natAbs_mul]
    -- The result follows from: foldl on mapped list ≤ c * foldl on original
    -- This requires showing that multiplying by |c| distributes over max
    calc (xs.map (c * ·)).foldl (fun acc a => max acc (Int.natAbs a)) (max 0 (Int.natAbs c * Int.natAbs x))
         ≤ Int.natAbs c * xs.foldl (fun acc a => max acc (Int.natAbs a)) (max 0 (Int.natAbs x)) := by
           -- Use foldl_max_le_bound' with bound = c * foldl xs
           have hbound := Int.natAbs c * xs.foldl (fun acc a => max acc (Int.natAbs a)) (max 0 (Int.natAbs x))
           -- Show init ≤ bound
           have hinit : max 0 (Int.natAbs c * Int.natAbs x) ≤ hbound := by
             calc max 0 (Int.natAbs c * Int.natAbs x)
                  ≤ Int.natAbs c * Int.natAbs x := Nat.le_max_right 0 _
                _ ≤ Int.natAbs c * max 0 (Int.natAbs x) := by
                    apply Nat.mul_le_mul_left
                    exact Nat.le_max_right 0 _
                _ ≤ Int.natAbs c * xs.foldl (fun acc a => max acc (Int.natAbs a)) (max 0 (Int.natAbs x)) := by
                    apply Nat.mul_le_mul_left
                    exact foldl_max_ge_init xs _
           -- Show each element ≤ bound
           have helem : ∀ z ∈ xs.map (c * ·), Int.natAbs z ≤ hbound := by
             intro z hz
             simp only [List.mem_map] at hz
             obtain ⟨y, hy, rfl⟩ := hz
             rw [Int.natAbs_mul]
             calc Int.natAbs c * Int.natAbs y
                  ≤ Int.natAbs c * xs.foldl (fun acc a => max acc (Int.natAbs a)) 0 := by
                    apply Nat.mul_le_mul_left
                    exact norm_mem_le xs y hy
                _ ≤ Int.natAbs c * xs.foldl (fun acc a => max acc (Int.natAbs a)) (max 0 (Int.natAbs x)) := by
                    apply Nat.mul_le_mul_left
                    exact foldl_max_mono xs 0 (max 0 (Int.natAbs x)) (Nat.zero_le _)
           exact foldl_max_le_bound' _ hbound _ hinit helem

end IceNine.Proofs.Core.NormProperties
