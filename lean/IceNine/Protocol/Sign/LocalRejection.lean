/-
# Local Rejection Sampling

Local rejection sampling for threshold Dilithium signing. Each signer applies
rejection sampling locally before sending their partial signature, with bounds
chosen so that any valid combination of partials automatically satisfies
global bounds.

## Key Invariant

If each of T signers produces z_i with ‖z_i‖∞ ≤ B_local, then the aggregate
z = Σ z_i satisfies ‖z‖∞ ≤ T · B_local ≤ B_global.

This eliminates global rejection as a distributed control-flow path.

## Effect Pattern

Following `NonceLifecycle.lean`, we provide:
- `RejectionOp` namespace: Pure operations for single/batch attempts
- `LocalSignResult`: Typed result structure
- Sequential and parallel loop variants

## Parallelization

Local rejection is trivially parallelizable:
1. **Across signers**: Each signer's loop is independent
2. **Within signer**: Batch multiple nonce candidates
3. **Within batch**: SIMD/vectorized norm checking

See Section 10 of the design document for parallelization strategies.
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.Core.ThresholdConfig
import IceNine.Protocol.Core.NormBounded
import IceNine.Protocol.Core.Error
import IceNine.Protocol.Sign.Types
import Mathlib

set_option autoImplicit false

namespace IceNine.Protocol.LocalRejection

open IceNine.Protocol
open IceNine.Protocol.ThresholdConfig
open IceNine.Protocol.NormBounded
open IceNine.Protocol.Error

/-!
## Local Sign Result

Result type for local rejection sampling operations.
-/

/-- Result of local rejection sampling.

    **Success**: Contains the partial signature z_i and attempt count.
    **Failure**: Contains error with attempt count for diagnostics. -/
inductive LocalSignResult (S : Scheme)
  | success
      (z_i : S.Secret)
      (hidingNonce : S.Secret)
      (bindingNonce : S.Secret)
      (attempts : Nat)
  | failure (err : LocalRejectionError S.PartyId)

/-- Check if result is success -/
def LocalSignResult.isSuccess {S : Scheme} : LocalSignResult S → Bool
  | .success _ _ _ _ => true
  | .failure _ => false

/-- Get z_i from successful result -/
def LocalSignResult.getZ {S : Scheme} : LocalSignResult S → Option S.Secret
  | .success z _ _ _ => some z
  | .failure _ => none

/-- Get attempt count from result -/
def LocalSignResult.attempts {S : Scheme} : LocalSignResult S → Nat
  | .success _ _ _ n => n
  | .failure (.maxAttemptsExceeded _ n _) => n
  | .failure _ => 0

/-!
## Parallelization Configuration

Configuration for parallel rejection sampling.
-/

/-- Configuration for parallel rejection sampling. -/
structure ParallelConfig where
  /-- Number of nonce candidates to sample per batch -/
  batchSize : Nat := 8
  /-- Whether to use SIMD-style evaluation -/
  useSimd : Bool := true
  /-- Maximum batches before giving up (0 = use maxLocalAttempts / batchSize) -/
  maxBatches : Nat := 0
  deriving Inhabited

/-- Default parallel configuration -/
def ParallelConfig.default : ParallelConfig :=
  { batchSize := 8, useSimd := true, maxBatches := 0 }

/-- High-throughput configuration: larger batches -/
def ParallelConfig.highThroughput : ParallelConfig :=
  { batchSize := 32, useSimd := true, maxBatches := 0 }

/-!
## Pure Operations (RejectionOp Namespace)

All operations are pure and composable. IO wrappers are provided separately.
-/

namespace RejectionOp

variable {S : Scheme}

/-- Compute z_i = y_hiding + ρ · y_binding + c · sk_i

    This is the partial signature response formula.

    **Inputs**:
    - `sk_i`: Signer's secret share
    - `challenge`: Fiat-Shamir challenge c
    - `hidingNonce`: Hiding nonce y_hiding (fresh random)
    - `bindingNonce`: Binding nonce y_binding (fresh random)
    - `bindingFactor`: Binding factor ρ_i

    **Output**: z_i = y_hiding + ρ · y_binding + c · sk_i -/
def computeZ [AddCommGroup S.Secret] [Module S.Scalar S.Secret] [SMul S.Challenge S.Secret]
    (sk_i : S.Secret)
    (challenge : S.Challenge)
    (hidingNonce : S.Secret)
    (bindingNonce : S.Secret)
    (bindingFactor : S.Scalar)
    : S.Secret :=
  hidingNonce + bindingFactor • bindingNonce + challenge • sk_i

/-- Single rejection attempt (pure). Atomic unit for parallel evaluation.

    Computes z_i and checks if it passes the local norm bound.

    **Returns**: `some z_i` if norm passes, `none` if rejected.

    This is designed to be called in parallel on multiple nonce candidates. -/
def tryOnce [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [SMul S.Challenge S.Secret] [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (sk_i : S.Secret)
    (challenge : S.Challenge)
    (hidingNonce : S.Secret)
    (bindingNonce : S.Secret)
    (bindingFactor : S.Scalar)
    : Option S.Secret :=
  let z := computeZ sk_i challenge hidingNonce bindingNonce bindingFactor
  if NormOp.checkLocal cfg z |>.isOk then some z else none

/-- Check result of a single attempt, with norm details. -/
def tryOnceWithDetails [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [SMul S.Challenge S.Secret] [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (sk_i : S.Secret)
    (challenge : S.Challenge)
    (hidingNonce : S.Secret)
    (bindingNonce : S.Secret)
    (bindingFactor : S.Scalar)
    : S.Secret × NormCheckResult :=
  let z := computeZ sk_i challenge hidingNonce bindingNonce bindingFactor
  (z, NormOp.checkLocal cfg z)

/-- Batch rejection attempt (pure, parallelizable).

    Evaluates multiple nonce candidates and returns the first success.

    **Inputs**:
    - `candidates`: List of (hidingNonce, bindingNonce) pairs

    **Returns**: `some (z_i, hidingNonce, bindingNonce, index)` for first success,
                 `none` if all candidates fail.

    This function is designed for SIMD/parallel evaluation:
    - All candidates can be evaluated in parallel
    - First-success semantics: stop at first valid z_i -/
def tryBatch [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [SMul S.Challenge S.Secret] [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (sk_i : S.Secret)
    (challenge : S.Challenge)
    (bindingFactor : S.Scalar)
    (candidates : List (S.Secret × S.Secret))
    : Option (S.Secret × S.Secret × S.Secret × Nat) :=
  let indexed := List.zip (List.range candidates.length) candidates
  indexed.findSome? fun (idx, (hid, binding)) =>
    match tryOnce cfg sk_i challenge hid binding bindingFactor with
    | some z => some (z, hid, binding, idx)
    | none => none

/-- Batch attempt with statistics. -/
def tryBatchWithStats [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [SMul S.Challenge S.Secret] [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (sk_i : S.Secret)
    (challenge : S.Challenge)
    (bindingFactor : S.Scalar)
    (candidates : List (S.Secret × S.Secret))
    : Option (S.Secret × S.Secret × S.Secret × Nat) × Nat :=
  -- Count successes for statistics (even though we only need first)
  let indexed := List.zip (List.range candidates.length) candidates
  let results := indexed.filterMap fun (idx, (hid, binding)) =>
    match tryOnce cfg sk_i challenge hid binding bindingFactor with
    | some z => some (z, hid, binding, idx)
    | none => none
  (results.head?, results.length)

end RejectionOp

/-!
## Sequential Loop

Baseline sequential rejection loop. Simple and correct.
-/

/-- Sequential local rejection loop.

    Samples nonces one at a time until finding valid z_i.
    This is the reference implementation; parallel variants are optimizations.

    **Inputs**:
    - `cfg`: Threshold configuration (contains maxLocalAttempts)
    - `sk_i`: Signer's secret share
    - `challenge`: Fiat-Shamir challenge
    - `bindingFactor`: Binding factor ρ_i
    - `sampleNonce`: IO action to sample a fresh nonce pair

    **Returns**: `LocalSignResult` with success or failure.

    **Linear guarantee**: Each call to `sampleNonce` produces fresh randomness.
    The caller must ensure `sampleNonce` uses CSPRNG. -/
def localRejectionLoop (S : Scheme)
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [SMul S.Challenge S.Secret] [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (partyId : S.PartyId)
    (sk_i : S.Secret)
    (challenge : S.Challenge)
    (bindingFactor : S.Scalar)
    (sampleNonce : IO (S.Secret × S.Secret))
    : IO (LocalSignResult S) := do
  let mut attempt : Nat := 0
  while attempt < cfg.maxLocalAttempts do
    let (hid, binding) ← sampleNonce
    match RejectionOp.tryOnce cfg sk_i challenge hid binding bindingFactor with
    | some z => return .success z hid binding (attempt + 1)
    | none => attempt := attempt + 1
  return .failure (.maxAttemptsExceeded partyId cfg.maxLocalAttempts cfg.localBound)

/-!
## Parallel Loop (Batched)

Batched rejection loop for better parallelism.
-/

/-- Parallel (batched) local rejection loop.

    Samples nonces in batches for better throughput:
    1. Sample `batchSize` nonce pairs at once
    2. Evaluate all candidates (can be parallel/SIMD)
    3. Return first success or continue with next batch

    **Inputs**:
    - `cfg`: Threshold configuration
    - `parallelCfg`: Parallelization settings
    - `sampleBatch`: IO action to sample a batch of nonce pairs

    **Returns**: `LocalSignResult` with success or failure.

    **Parallelization opportunity**: The `sampleBatch` action can parallelize
    CSPRNG sampling, and `tryBatch` can use SIMD/GPU for norm checking. -/
def localRejectionLoopParallel (S : Scheme)
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [SMul S.Challenge S.Secret] [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (parallelCfg : ParallelConfig)
    (partyId : S.PartyId)
    (sk_i : S.Secret)
    (challenge : S.Challenge)
    (bindingFactor : S.Scalar)
    (sampleBatch : Nat → IO (List (S.Secret × S.Secret)))
    : IO (LocalSignResult S) := do
  let maxBatches :=
    if parallelCfg.maxBatches > 0 then parallelCfg.maxBatches
    else (cfg.maxLocalAttempts + parallelCfg.batchSize - 1) / parallelCfg.batchSize
  let mut batch : Nat := 0
  let mut totalAttempts : Nat := 0
  while batch < maxBatches do
    let candidates ← sampleBatch parallelCfg.batchSize
    totalAttempts := totalAttempts + candidates.length
    match RejectionOp.tryBatch cfg sk_i challenge bindingFactor candidates with
    | some (z, hid, binding, _idx) =>
        return .success z hid binding totalAttempts
    | none => batch := batch + 1
  return .failure (.maxAttemptsExceeded partyId totalAttempts cfg.localBound)

/-!
## Pure Batch Evaluation

For use in contexts where IO is not available (proofs, simulation).
-/

/-- Pure batch evaluation for testing/simulation.

    Given a pre-generated list of nonce candidates, find the first
    that produces a valid z_i.

    **Use case**: Testing, proof simulation, deterministic replay. -/
def localRejectionPure (S : Scheme)
    [AddCommGroup S.Secret] [Module S.Scalar S.Secret]
    [SMul S.Challenge S.Secret] [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (partyId : S.PartyId)
    (sk_i : S.Secret)
    (challenge : S.Challenge)
    (bindingFactor : S.Scalar)
    (allCandidates : List (S.Secret × S.Secret))
    : LocalSignResult S :=
  let maxAttempts := min cfg.maxLocalAttempts allCandidates.length
  let candidates := allCandidates.take maxAttempts
  match RejectionOp.tryBatch cfg sk_i challenge bindingFactor candidates with
  | some (z, hid, binding, idx) =>
      .success z hid binding (idx + 1)
  | none =>
      .failure (.maxAttemptsExceeded partyId maxAttempts cfg.localBound)

/-!
## Result Utilities
-/

/-- Convert LocalSignResult to Except for monadic composition -/
def LocalSignResult.toExcept {S : Scheme} : LocalSignResult S →
    Except (LocalRejectionError S.PartyId) (S.Secret × S.Secret × S.Secret × Nat)
  | .success z hid binding attempts => .ok (z, hid, binding, attempts)
  | .failure err => .error err

/-- Get statistics from result -/
structure RejectionStats where
  /-- Number of attempts made -/
  attempts : Nat
  /-- Whether rejection succeeded -/
  succeeded : Bool
  /-- Local bound used -/
  localBound : Nat
  deriving Repr

/-- Extract statistics from result -/
def LocalSignResult.stats {S : Scheme} (cfg : ThresholdConfig) : LocalSignResult S → RejectionStats
  | .success _ _ _ n => { attempts := n, succeeded := true, localBound := cfg.localBound }
  | .failure _ => { attempts := cfg.maxLocalAttempts, succeeded := false, localBound := cfg.localBound }

end IceNine.Protocol.LocalRejection
