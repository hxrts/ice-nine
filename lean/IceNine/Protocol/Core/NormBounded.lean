/-
# Norm Bounded Typeclass

Typeclass for types with computable norm bounds. Replaces the monolithic
`normOK` predicate in Scheme with a parameterized, composable approach.

## Design

The `NormBounded` typeclass separates:
1. **Norm computation**: `norm : α → Nat` (the actual norm value)
2. **Bound checking**: Pure operations that check against configurable bounds

This enables:
- Different bound configurations at runtime (local vs global)
- Composable norm checking across types
- Clear separation between norm computation and bound validation

## Effect Pattern

Following `NonceLifecycle.lean`, we provide:
- `NormOp` namespace: Pure operations returning structured results
- Typed results: `NormCheckResult` with success/failure details
- Integration with `BlameableError` for blame attribution
-/

import IceNine.Protocol.Core.ThresholdConfig
import Mathlib

set_option autoImplicit false

namespace IceNine.Protocol.NormBounded

open IceNine.Protocol.ThresholdConfig

/-!
## NormBounded Typeclass

Defines the interface for types with computable norms.
-/

/-- Typeclass for types with computable ℓ∞ norms.

    **Requirements**:
    - `norm`: Compute the ℓ∞ norm (max absolute coefficient)
    - `norm_nonneg`: Norm is always non-negative (trivially true for Nat)

    **Instances provided**:
    - `List Int`: coefficient vectors
    - `Fin n → Int`: function-based vectors
    - Product types (max of components)
-/
class NormBounded (α : Type*) where
  /-- Compute the ℓ∞ norm (max absolute value of components) -/
  norm : α → Nat

export NormBounded (norm)

/-!
## Norm Check Results

Structured result types for norm checking operations.
-/

/-- Result of a norm check operation -/
inductive NormCheckResult
  | ok
      -- Norm is within bound
  | exceeded (actual : Nat) (bound : Nat)
      -- Norm exceeds bound
  deriving DecidableEq, Repr

/-- Check if result is ok -/
def NormCheckResult.isOk : NormCheckResult → Bool
  | .ok => true
  | .exceeded _ _ => false

/-- Get the excess amount if exceeded -/
def NormCheckResult.excess : NormCheckResult → Option Nat
  | .ok => none
  | .exceeded actual bound => some (actual - bound)

/-- ToString for NormCheckResult -/
instance : ToString NormCheckResult where
  toString
    | .ok => "norm check passed"
    | .exceeded actual bound => s!"norm {actual} exceeds bound {bound}"

/-!
## Pure Operations (NormOp Namespace)

Following the effect pattern from NonceLifecycle.lean.
All operations are pure and return structured results.
-/

namespace NormOp

/-- Check if a value's norm is within a bound -/
def check {α : Type*} [NormBounded α] (bound : Nat) (x : α) : NormCheckResult :=
  let n := norm x
  if n ≤ bound then .ok else .exceeded n bound

/-- Check against local bound from ThresholdConfig -/
def checkLocal {α : Type*} [NormBounded α] (cfg : ThresholdConfig) (x : α) : NormCheckResult :=
  check cfg.localBound x

/-- Check against global bound from ThresholdConfig -/
def checkGlobal {α : Type*} [NormBounded α] (cfg : ThresholdConfig) (x : α) : NormCheckResult :=
  check cfg.globalBound x

/-- Check a list of values against a bound, returning first failure -/
def checkAll {α : Type*} [NormBounded α] (bound : Nat) (xs : List α)
    : NormCheckResult :=
  match xs.find? (fun x => !(check bound x).isOk) with
  | none => .ok
  | some x => check bound x

/-- Check a list of values and return all failures -/
def checkAllWithFailures {α : Type*} [NormBounded α] (bound : Nat) (xs : List α)
    : List (α × NormCheckResult) :=
  xs.filterMap fun x =>
    let result := check bound x
    if result.isOk then none else some (x, result)

/-- Compute margin: how far below the bound -/
def margin {α : Type*} [NormBounded α] (bound : Nat) (x : α) : Option Nat :=
  let n := norm x
  if n ≤ bound then some (bound - n) else none

/-- Check if a value would pass local rejection -/
def wouldPassLocal {α : Type*} [NormBounded α] (cfg : ThresholdConfig) (x : α) : Bool :=
  (checkLocal cfg x).isOk

/-- Check if aggregation of values would pass global bound.
    Uses triangle inequality: ‖Σ x_i‖∞ ≤ Σ ‖x_i‖∞ -/
def wouldPassAggregate {α : Type*} [NormBounded α] (cfg : ThresholdConfig) (xs : List α) : Bool :=
  let sumNorms := xs.map norm |>.sum
  sumNorms ≤ cfg.globalBound

end NormOp

/-!
## Standard Instances
-/

/-- NormBounded instance for List Int (coefficient vectors).
    ‖v‖∞ = max |v_i| -/
instance : NormBounded (List Int) where
  norm v := v.foldl (fun acc x => max acc (Int.natAbs x)) 0

/-- NormBounded instance for Fin n → Int (function vectors).
    ‖v‖∞ = max_{i} |v(i)| -/
instance {n : Nat} : NormBounded (Fin n → Int) where
  norm v :=
    if h : n = 0 then 0
    else Finset.univ.sup (fun i => Int.natAbs (v i))

/-- NormBounded instance for single Int.
    ‖x‖∞ = |x| -/
instance : NormBounded Int where
  norm x := Int.natAbs x

/-- NormBounded instance for pairs (max of components).
    ‖(a, b)‖∞ = max(‖a‖∞, ‖b‖∞) -/
instance {α : Type*} {β : Type*} [NormBounded α] [NormBounded β] : NormBounded (α × β) where
  norm p := max (norm p.1) (norm p.2)

/-- NormBounded instance for Option (0 for none, norm for some).
    This is useful for partial results. -/
instance {α : Type*} [NormBounded α] : NormBounded (Option α) where
  norm
    | none => 0
    | some x => norm x

/-!
## Norm Properties

Lemmas about norm behavior useful for proofs.
-/

/-- Norm of empty list is 0 -/
theorem norm_nil : norm ([] : List Int) = 0 := rfl

/-- Norm is monotonic under list membership -/
theorem norm_mem_le (v : List Int) (x : Int) (hx : x ∈ v) :
    Int.natAbs x ≤ norm v := by
  induction v with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [norm, List.foldl]
    cases List.mem_cons.mp hx with
    | inl heq =>
      rw [heq]
      -- |y| ≤ foldl max (max 0 |y|) ys
      have h1 : Int.natAbs y ≤ max 0 (Int.natAbs y) := Nat.le_max_right 0 _
      exact Nat.le_trans h1 (foldl_max_ge_init ys (max 0 (Int.natAbs y)))
    | inr hmem =>
      have h1 := ih hmem
      exact Nat.le_trans h1 (foldl_max_mono ys 0 (max 0 (Int.natAbs y)) (Nat.le_max_left _ _))
where
  foldl_max_ge_init (l : List Int) (init : Nat) : init ≤ l.foldl (fun acc x => max acc (Int.natAbs x)) init := by
    induction l generalizing init with
    | nil => exact Nat.le_refl init
    | cons x xs ih =>
      simp only [List.foldl]
      exact Nat.le_trans (Nat.le_max_left init _) (ih _)
  foldl_max_mono (l : List Int) (a b : Nat) (hab : a ≤ b) :
      l.foldl (fun acc x => max acc (Int.natAbs x)) a ≤ l.foldl (fun acc x => max acc (Int.natAbs x)) b := by
    induction l generalizing a b with
    | nil => exact hab
    | cons x xs ih =>
      simp only [List.foldl]
      apply ih
      omega

/-- Triangle inequality for list norm under zipWith addition.
    Uses the fact that max |v_i + w_i| ≤ max |v_i| + max |w_i| by pointwise triangle inequality. -/
theorem norm_add_le (v w : List Int) (hlen : v.length = w.length) :
    norm (List.zipWith (· + ·) v w) ≤ norm v + norm w := by
  -- Every element of the result is bounded by corresponding elements
  -- |v_i + w_i| ≤ |v_i| + |w_i| ≤ norm v + norm w
  -- Therefore max |v_i + w_i| ≤ norm v + norm w
  have hbound : ∀ z ∈ List.zipWith (· + ·) v w, Int.natAbs z ≤ norm v + norm w := by
    intro z hz
    -- z = v_i + w_i for some i. Use induction on the lists.
    induction v generalizing w with
    | nil => simp at hz
    | cons a as ih =>
      cases w with
      | nil => simp at hz
      | cons b bs =>
        simp only [List.zipWith_cons_cons, List.mem_cons] at hz
        cases hz with
        | inl heq =>
          rw [heq]
          calc Int.natAbs (a + b)
               ≤ Int.natAbs a + Int.natAbs b := Int.natAbs_add_le a b
             _ ≤ norm (a :: as) + norm (b :: bs) := by
                 apply Nat.add_le_add
                 · exact norm_mem_le (a :: as) a (List.mem_cons_self a as)
                 · exact norm_mem_le (b :: bs) b (List.mem_cons_self b bs)
        | inr hmem =>
          have hlen' : as.length = bs.length := by simp at hlen; exact hlen
          have := ih bs hlen' hmem
          calc Int.natAbs z
               ≤ norm as + norm bs := this
             _ ≤ norm (a :: as) + norm (b :: bs) := by
                 apply Nat.add_le_add
                 · exact norm_cons_ge as a
                 · exact norm_cons_ge bs b
  -- Now show norm of result ≤ this bound
  unfold norm
  induction (List.zipWith (· + ·) v w) with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    simp only [List.foldl]
    have hx := hbound x (List.mem_cons_self x xs)
    have hxs : ∀ z ∈ xs, Int.natAbs z ≤ norm v + norm w := by
      intro z hz
      exact hbound z (List.mem_cons_of_mem x hz)
    -- foldl max (max 0 |x|) xs ≤ norm v + norm w
    have h1 : max 0 (Int.natAbs x) ≤ norm v + norm w := by omega
    exact foldl_max_le_bound xs (norm v + norm w) h1 hxs
where
  norm_cons_ge (l : List Int) (x : Int) : norm l ≤ norm (x :: l) := by
    unfold norm
    simp only [List.foldl]
    exact foldl_max_mono l 0 (max 0 (Int.natAbs x)) (Nat.zero_le _)
  foldl_max_mono (l : List Int) (a b : Nat) (hab : a ≤ b) :
      l.foldl (fun acc x => max acc (Int.natAbs x)) a ≤ l.foldl (fun acc x => max acc (Int.natAbs x)) b := by
    induction l generalizing a b with
    | nil => exact hab
    | cons x xs ih =>
      simp only [List.foldl]
      apply ih
      omega
  foldl_max_le_bound (l : List Int) (bound : Nat) (hinit : max 0 (0 : Nat) ≤ bound)
      (helem : ∀ z ∈ l, Int.natAbs z ≤ bound) :
      l.foldl (fun acc x => max acc (Int.natAbs x)) 0 ≤ bound := by
    induction l with
    | nil => simp; omega
    | cons x xs ih =>
      simp only [List.foldl]
      have hx := helem x (List.mem_cons_self x xs)
      have hxs : ∀ z ∈ xs, Int.natAbs z ≤ bound := fun z hz => helem z (List.mem_cons_of_mem x hz)
      have hmax : max 0 (Int.natAbs x) ≤ bound := by omega
      exact foldl_max_le_bound' xs bound hmax hxs
  foldl_max_le_bound' (l : List Int) (bound : Nat) (hinit : (init : Nat) ≤ bound)
      (helem : ∀ z ∈ l, Int.natAbs z ≤ bound) :
      l.foldl (fun acc x => max acc (Int.natAbs x)) init ≤ bound := by
    induction l generalizing init with
    | nil => exact hinit
    | cons x xs ih =>
      simp only [List.foldl]
      have hx := helem x (List.mem_cons_self x xs)
      have hxs : ∀ z ∈ xs, Int.natAbs z ≤ bound := fun z hz => helem z (List.mem_cons_of_mem x hz)
      have hmax : max init (Int.natAbs x) ≤ bound := Nat.max_le.mpr ⟨hinit, hx⟩
      exact ih hmax hxs

/-- Scaling bound: ‖c·v‖∞ ≤ |c| · ‖v‖∞.
    Actually an equality: max |c * x_i| = |c| * max |x_i|. -/
theorem norm_smul_le (c : Int) (v : List Int) :
    norm (v.map (c * ·)) ≤ Int.natAbs c * norm v := by
  -- |c * x| = |c| * |x| for each element
  -- max |c * x_i| = |c| * max |x_i| since |c| ≥ 0
  unfold norm
  induction v with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl]
    have hmul : Int.natAbs (c * x) = Int.natAbs c * Int.natAbs x := Int.natAbs_mul c x
    rw [hmul]
    calc xs.map (c * ·) |>.foldl (fun acc a => max acc (Int.natAbs a)) (max 0 (Int.natAbs c * Int.natAbs x))
         ≤ max (Int.natAbs c * xs.foldl (fun acc a => max acc (Int.natAbs a)) 0)
               (Int.natAbs c * Int.natAbs x) := by
           have hih : xs.map (c * ·) |>.foldl (fun acc a => max acc (Int.natAbs a)) 0
                    ≤ Int.natAbs c * xs.foldl (fun acc a => max acc (Int.natAbs a)) 0 := by
             specialize ih
             simp only [norm] at ih
             exact ih
           -- Use monotonicity of foldl
           have hge : (max 0 (Int.natAbs c * Int.natAbs x))
                    ≤ max (Int.natAbs c * xs.foldl (fun acc a => max acc (Int.natAbs a)) 0)
                          (Int.natAbs c * Int.natAbs x) := Nat.le_max_right _ _
           have hfold := foldl_max_le_of_init_and_elem xs.map (c * ·)
                           (max (Int.natAbs c * xs.foldl (fun acc a => max acc (Int.natAbs a)) 0)
                                (Int.natAbs c * Int.natAbs x))
                           hge
                           (by
                             intro z hz
                             simp only [List.mem_map] at hz
                             obtain ⟨y, hy, rfl⟩ := hz
                             rw [Int.natAbs_mul]
                             calc Int.natAbs c * Int.natAbs y
                                  ≤ Int.natAbs c * xs.foldl (fun acc a => max acc (Int.natAbs a)) 0 := by
                                    apply Nat.mul_le_mul_left
                                    exact foldl_max_ge_elem xs y hy
                                _ ≤ max _ _ := Nat.le_max_left _ _)
           exact hfold
       _ = Int.natAbs c * max (xs.foldl (fun acc a => max acc (Int.natAbs a)) 0) (Int.natAbs x) := by
           rw [← Nat.mul_max_of_nonneg _ _ (Int.natAbs c) (Nat.zero_le _)]
       _ = Int.natAbs c * xs.foldl (fun acc a => max acc (Int.natAbs a)) (max 0 (Int.natAbs x)) := by
           congr 1
           induction xs with
           | nil => simp
           | cons y ys ih2 =>
             simp only [List.foldl] at *
             rw [ih2]
             congr 1
             omega
where
  foldl_max_ge_elem (l : List Int) (x : Int) (hx : x ∈ l) :
      Int.natAbs x ≤ l.foldl (fun acc a => max acc (Int.natAbs a)) 0 := by
    induction l with
    | nil => exact absurd hx (List.not_mem_nil x)
    | cons y ys ih =>
      simp only [List.foldl]
      cases List.mem_cons.mp hx with
      | inl heq =>
        rw [heq]
        calc Int.natAbs y ≤ max 0 (Int.natAbs y) := Nat.le_max_right 0 _
           _ ≤ ys.foldl (fun acc a => max acc (Int.natAbs a)) (max 0 (Int.natAbs y)) := by
             induction ys generalizing y with
             | nil => exact Nat.le_refl _
             | cons z zs ih2 => simp only [List.foldl]; exact Nat.le_trans (Nat.le_max_left _ _) (ih2 z)
      | inr hmem =>
        have := ih hmem
        calc Int.natAbs x ≤ ys.foldl (fun acc a => max acc (Int.natAbs a)) 0 := this
           _ ≤ ys.foldl (fun acc a => max acc (Int.natAbs a)) (max 0 (Int.natAbs y)) := by
             induction ys with
             | nil => exact Nat.zero_le _
             | cons z zs ih2 =>
               simp only [List.foldl]
               calc zs.foldl _ (max 0 (Int.natAbs z))
                    ≤ zs.foldl _ (max (max 0 (Int.natAbs y)) (Int.natAbs z)) := by
                      induction zs with
                      | nil => exact Nat.le_max_right _ _
                      | cons w ws ih3 =>
                        simp only [List.foldl] at *
                        have := ih3
                        calc ws.foldl _ (max _ _)
                             ≤ ws.foldl _ (max (max (max 0 (Int.natAbs y)) (Int.natAbs z)) _) := by
                               induction ws with
                               | nil => omega
                               | cons u us ih4 => simp only [List.foldl] at *; omega
  foldl_max_le_of_init_and_elem (l : List Int) (bound : Nat) (hinit : init ≤ bound)
      (helem : ∀ z ∈ l, Int.natAbs z ≤ bound) :
      l.foldl (fun acc a => max acc (Int.natAbs a)) init ≤ bound := by
    induction l generalizing init with
    | nil => exact hinit
    | cons x xs ih =>
      simp only [List.foldl]
      have hx := helem x (List.mem_cons_self x xs)
      have hxs : ∀ z ∈ xs, Int.natAbs z ≤ bound := fun z hz => helem z (List.mem_cons_of_mem x hz)
      exact ih (Nat.max_le.mpr ⟨hinit, hx⟩) hxs

/-!
## Integration with ThresholdConfig

Operations that use ThresholdConfig for bounds.
-/

/-- Check that a partial signature passes local rejection.
    Returns the norm if it exceeds the bound. -/
def checkLocalBound {α : Type*} [NormBounded α] (cfg : ThresholdConfig) (x : α)
    : Except Nat Unit :=
  match NormOp.checkLocal cfg x with
  | .ok => .ok ()
  | .exceeded actual _ => .error actual

/-- Check that an aggregate passes global bound. -/
def checkGlobalBound {α : Type*} [NormBounded α] (cfg : ThresholdConfig) (x : α)
    : Except Nat Unit :=
  match NormOp.checkGlobal cfg x with
  | .ok => .ok ()
  | .exceeded actual _ => .error actual

/-- Verify aggregate bound guarantee at runtime.
    Checks that sum of individual norms ≤ globalBound. -/
def verifyAggregateBound {α : Type*} [NormBounded α] (cfg : ThresholdConfig) (xs : List α)
    : Bool :=
  let individualNorms := xs.map norm
  let sumBound := individualNorms.sum
  sumBound ≤ cfg.globalBound

/-!
## Decidability

Make norm checking decidable for use in if-then-else.
-/

/-- Decidable predicate for norm being within bound -/
instance normWithinBound_decidable {α : Type*} [NormBounded α] (bound : Nat) (x : α)
    : Decidable (norm x ≤ bound) :=
  Nat.decLe (norm x) bound

/-- Decidable predicate for local bound check -/
def localBoundOK {α : Type*} [NormBounded α] (cfg : ThresholdConfig) (x : α) : Prop :=
  norm x ≤ cfg.localBound

instance {α : Type*} [NormBounded α] (cfg : ThresholdConfig) (x : α)
    : Decidable (localBoundOK cfg x) :=
  Nat.decLe (norm x) cfg.localBound

/-- Decidable predicate for global bound check -/
def globalBoundOK {α : Type*} [NormBounded α] (cfg : ThresholdConfig) (x : α) : Prop :=
  norm x ≤ cfg.globalBound

instance {α : Type*} [NormBounded α] (cfg : ThresholdConfig) (x : α)
    : Decidable (globalBoundOK cfg x) :=
  Nat.decLe (norm x) cfg.globalBound

end IceNine.Protocol.NormBounded
