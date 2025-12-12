/-
# Sample transcript generation and tests

Convenient `#eval` snippets and tests for the local rejection signing system.

This file demonstrates:
- ThresholdConfig usage and construction
- NormBounded typeclass operations
- Local rejection sampling
- Validated aggregation with blame collection
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.Core.ThresholdConfig
import IceNine.Protocol.Core.NormBounded
import IceNine.Protocol.DKG.Core
import IceNine.Protocol.Sign.Types
import IceNine.Protocol.Sign.Core
import IceNine.Protocol.Sign.LocalRejection
import IceNine.Protocol.Sign.ValidatedAggregation
import IceNine.Instances
import IceNine.Norms

open IceNine.Protocol
open IceNine.Protocol.NormBounded
open IceNine.Instances
open IceNine.Norms

/-!
## ThresholdConfig Tests

Test the ThresholdConfig construction and validation.
-/

/-- Test default threshold calculation (2/3+1) -/
#eval do
  IO.println s!"defaultThreshold 3 = {defaultThreshold 3}"  -- Should be 3
  IO.println s!"defaultThreshold 4 = {defaultThreshold 4}"  -- Should be 3
  IO.println s!"defaultThreshold 7 = {defaultThreshold 7}"  -- Should be 5
  IO.println s!"defaultThreshold 10 = {defaultThreshold 10}"  -- Should be 7
  IO.println s!"defaultThreshold 100 = {defaultThreshold 100}"  -- Should be 67

/-- Test ThresholdConfig construction -/
def testThresholdConfig : IO Unit := do
  -- 4 parties, global bound 1000
  let cfg := ThresholdConfig.mk' 4 1000
  IO.println s!"4-party config:"
  IO.println s!"  totalParties = {cfg.totalParties}"
  IO.println s!"  threshold = {cfg.threshold}"
  IO.println s!"  maxSigners = {cfg.maxSigners}"
  IO.println s!"  globalBound = {cfg.globalBound}"
  IO.println s!"  localBound = {cfg.localBound}"

  -- Custom 5-of-7 threshold
  let cfg2 := ThresholdConfig.mk' 7 1000 (t := 5) (maxSigners := 5)
  IO.println s!"\n5-of-7 config:"
  IO.println s!"  totalParties = {cfg2.totalParties}"
  IO.println s!"  threshold = {cfg2.threshold}"
  IO.println s!"  localBound = {cfg2.localBound}"

#eval testThresholdConfig

/-!
## NormBounded Tests

Test the NormBounded typeclass operations.
-/

/-- Test norm computation for integer lists -/
def testNormBounded : IO Unit := do
  -- Test list norm
  let v1 : List Int := [1, -3, 2, 5, -4]
  let norm1 := listIntNorm v1
  IO.println s!"Norm of {v1} = {norm1}"  -- Should be 5

  let v2 : List Int := [0, 0, 0]
  let norm2 := listIntNorm v2
  IO.println s!"Norm of {v2} = {norm2}"  -- Should be 0

  let v3 : List Int := [-10, 5, 8]
  let norm3 := listIntNorm v3
  IO.println s!"Norm of {v3} = {norm3}"  -- Should be 10

  -- Test norm checking
  let result1 := NormOp.check 5 v1
  IO.println s!"Check {v1} against bound 5: {repr result1}"  -- Should be ok

  let result2 := NormOp.check 4 v1
  IO.println s!"Check {v1} against bound 4: {repr result2}"  -- Should be exceeded

#eval testNormBounded

/-!
## Local Rejection Tests

Test the pure rejection sampling operations.
-/

/-- Simulate a local rejection attempt with mock data -/
def testLocalRejection : IO Unit := do
  let cfg := ThresholdConfig.mk' 4 100  -- 4 parties, global bound 100, local bound ~33

  IO.println s!"Local rejection test:"
  IO.println s!"  localBound = {cfg.localBound}"

  -- Simulate z_i values that would pass/fail local bound
  let z_pass : List Int := [10, -15, 5, 20, -10]
  let z_fail : List Int := [10, -50, 5, 20, -10]  -- norm = 50 > 33

  let passResult := NormOp.checkLocal cfg z_pass
  let failResult := NormOp.checkLocal cfg z_fail

  IO.println s!"  z_pass norm = {listIntNorm z_pass}, check = {repr passResult}"
  IO.println s!"  z_fail norm = {listIntNorm z_fail}, check = {repr failResult}"

#eval testLocalRejection

/-!
## Aggregate Bound Tests

Test that valid local shares aggregate to valid global signature.
-/

/-- Test aggregate bound guarantee -/
def testAggregateBound : IO Unit := do
  let cfg := ThresholdConfig.mk' 4 120  -- 4 parties, global bound 120, local bound 40

  IO.println s!"Aggregate bound test:"
  IO.println s!"  globalBound = {cfg.globalBound}"
  IO.println s!"  localBound = {cfg.localBound}"
  IO.println s!"  threshold = {cfg.threshold}"

  -- 3 shares, each with norm ≤ 40
  let z1 : List Int := [30, -20, 10, -15]
  let z2 : List Int := [-25, 35, -10, 20]
  let z3 : List Int := [15, -10, 25, -30]

  IO.println s!"\n  Share norms:"
  IO.println s!"    z1 norm = {listIntNorm z1}"
  IO.println s!"    z2 norm = {listIntNorm z2}"
  IO.println s!"    z3 norm = {listIntNorm z3}"

  -- Aggregate: z = z1 + z2 + z3
  let z_agg := ((z1.zip z2).zip z3).map fun ((a, b), c) => a + b + c
  let aggNorm := listIntNorm z_agg

  IO.println s!"\n  Aggregate:"
  IO.println s!"    z_agg = {z_agg}"
  IO.println s!"    z_agg norm = {aggNorm}"
  IO.println s!"    Within global bound? {aggNorm ≤ cfg.globalBound}"

  -- Note: Actual norm may be less than 3 * 40 = 120 due to cancellation
  -- In this case: z_agg = [20, 5, 25, -25], norm = 25 ≤ 120

#eval testAggregateBound

/-!
## Configuration Examples from Design Doc
-/

/-- Dilithium-style configuration examples -/
def testDilithiumConfigs : IO Unit := do
  -- Dilithium2 global bound: γ₁ - β = 2^17 - 78 ≈ 131000
  let dilithiumBound := 131000

  IO.println "Dilithium-style configurations:"

  -- 4-party config
  let cfg4 := ThresholdConfig.mk' 4 dilithiumBound
  IO.println s!"\n4-party (3-of-4):"
  IO.println s!"  localBound = {cfg4.localBound}"  -- ~43666
  IO.println s!"  Expected attempts per signer: ~4"

  -- 10-party config
  let cfg10 := ThresholdConfig.mk' 10 dilithiumBound
  IO.println s!"\n10-party (7-of-10):"
  IO.println s!"  localBound = {cfg10.localBound}"  -- ~18714
  IO.println s!"  Expected attempts per signer: ~7"

  -- 100-party config
  let cfg100 := ThresholdConfig.mk' 100 dilithiumBound
  IO.println s!"\n100-party (67-of-100):"
  IO.println s!"  localBound = {cfg100.localBound}"  -- ~1955
  IO.println s!"  Expected attempts per signer: ~67"

#eval testDilithiumConfigs

/-!
## Summary

These tests demonstrate the local rejection signing system:

1. **ThresholdConfig**: Configurable threshold parameters with proof obligations
2. **NormBounded**: Typeclass-based norm computation and checking
3. **Local Rejection**: Per-signer rejection sampling within local bounds
4. **Aggregate Guarantee**: Valid local shares compose to valid global signature

Key invariant: If T signers produce z_i with ‖z_i‖∞ ≤ B_local, then
z = Σz_i satisfies ‖z‖∞ ≤ T · B_local ≤ B_global.

This eliminates global rejection as a distributed control-flow path.
-/
