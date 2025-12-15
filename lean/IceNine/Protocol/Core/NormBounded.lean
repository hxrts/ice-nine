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

-- Suppress duplication warnings (namespace `NormBounded` contains the class `NormBounded`).
set_option linter.dupNamespace false

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
    if _h : n = 0 then 0
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

Lemmas about norm behavior are in `Proofs/Core/NormProperties.lean`.
-/

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
