/-
# Threshold Configuration

Configuration structure for threshold signing with local rejection sampling.
Defines the relationship between local and global norm bounds that enables
restart-free signing.

## Key Invariant

If each of T signers produces z_i with ‖z_i‖∞ ≤ B_local, then the aggregate
z = Σ z_i satisfies ‖z‖∞ ≤ T · B_local ≤ B_global.

This eliminates global rejection as a distributed control-flow path.

## Usage

```lean
-- Create configuration for 5 parties with 2/3+1 threshold
let cfg := ThresholdConfig.mk 5 131072  -- defaults to t = 4

-- Custom threshold
let cfg := ThresholdConfig.mk 7 131072 (t := 5)
```
-/

import Mathlib

set_option autoImplicit false

namespace IceNine.Protocol.ThresholdConfig

/-!
## Default Threshold Computation

The default threshold is 2/3+1, which ensures honest majority for BFT protocols.
This can be overridden for different security requirements.
-/

/-- Compute default threshold for 2/3+1 honest majority requirement.

    For n parties, returns ⌊2n/3⌋ + 1, which is the minimum number of
    honest parties needed to ensure byzantine fault tolerance.

    Examples:
    - n = 3: t = 3 (all must be honest)
    - n = 4: t = 3
    - n = 5: t = 4
    - n = 6: t = 5
    - n = 7: t = 5 -/
def defaultThreshold (n : Nat) : Nat := 2 * n / 3 + 1

/-- Default threshold is at least 1 for any positive n. -/
theorem defaultThreshold_pos (n : Nat) (hn : n > 0) : defaultThreshold n ≥ 1 := by
  simp only [defaultThreshold]
  omega

/-- Default threshold never exceeds n (for n ≥ 1). -/
theorem defaultThreshold_le (n : Nat) (hn : n ≥ 1) : defaultThreshold n ≤ n := by
  simp only [defaultThreshold]
  omega

/-!
## Threshold Configuration Structure

Bundles all parameters for threshold signing with local rejection:
- Party counts (total, threshold, max signers)
- Norm bounds (global and derived local)
- Validity proofs (ensure configuration is consistent)
-/

/-- Configuration for threshold signing with local rejection.

    The key relationship: localBound * maxSigners ≤ globalBound
    This guarantees any T valid partials aggregate to a valid signature.

    **Parameters**:
    - `totalParties`: Total number of parties in the scheme
    - `threshold`: Minimum parties needed for reconstruction
    - `maxSigners`: Maximum partials that will be aggregated (usually = threshold)
    - `globalBound`: Global Dilithium bound (γ₁ - β)
    - `localBound`: Per-signer local bound (derived: globalBound / maxSigners)
    - `maxLocalAttempts`: Maximum local rejection attempts before giving up

    **Validity proofs**: The proofs ensure the configuration is consistent.
    They are auto-filled by omega when possible. -/
structure ThresholdConfig where
  /-- Total number of parties in the scheme -/
  totalParties : Nat
  /-- Threshold for reconstruction (minimum honest parties) -/
  threshold : Nat
  /-- Maximum partials that will be aggregated (usually = threshold) -/
  maxSigners : Nat
  /-- Global Dilithium bound (γ₁ - β) -/
  globalBound : Nat
  /-- Per-signer local bound (derived: globalBound / maxSigners) -/
  localBound : Nat := globalBound / maxSigners
  /-- Maximum local rejection attempts before giving up -/
  maxLocalAttempts : Nat := 256
  /-- Validity: threshold achievable with honest majority -/
  threshold_le_total : threshold ≤ totalParties
  /-- Validity: we aggregate at least threshold partials -/
  maxSigners_ge_threshold : maxSigners ≥ threshold
  /-- Validity: local bounds compose to global -/
  local_global_bound : localBound * maxSigners ≤ globalBound
  deriving Repr

/-!
## Configuration Constructor

Smart constructor with defaults and automatic proof obligations.
-/

/-- Create a threshold configuration with explicit parameters.

    Parameters:
    - n: total number of parties
    - globalBound: Dilithium norm bound (γ₁ - β)
    - t: threshold (minimum parties needed), defaults to 2/3+1
    - maxSigners: maximum partials aggregated (usually = t)

    The proofs are filled automatically by omega when possible.

    **Example**:
    ```lean
    -- 5-party scheme with default threshold (4)
    let cfg := ThresholdConfig.create 5 131072

    -- 7-party scheme with custom threshold (5)
    let cfg := ThresholdConfig.create 7 131072 (t := 5)
    ```
-/
def ThresholdConfig.create
    (n : Nat)
    (globalBound : Nat)
    (t : Nat := defaultThreshold n)
    (maxSigners : Nat := t)
    (maxLocalAttempts : Nat := 256)
    (h1 : t ≤ n := by omega)
    (h2 : maxSigners ≥ t := by omega)
    (h3 : (globalBound / maxSigners) * maxSigners ≤ globalBound := by omega)
    : ThresholdConfig :=
  { totalParties := n
    threshold := t
    maxSigners := maxSigners
    globalBound := globalBound
    localBound := globalBound / maxSigners
    maxLocalAttempts := maxLocalAttempts
    threshold_le_total := h1
    maxSigners_ge_threshold := h2
    local_global_bound := h3 }

/-!
## Configuration Accessors and Derived Values
-/

/-- Number of tolerable faulty parties: n - t -/
def ThresholdConfig.maxFaulty (cfg : ThresholdConfig) : Nat :=
  cfg.totalParties - cfg.threshold

/-- Threshold for abort consensus: f + 1 where f = maxFaulty.

    This ensures at least one honest party agreed to abort, preventing
    a coalition of f malicious parties from forcing spurious aborts.

    Examples (using default 2/3+1 threshold):
    - n = 3, t = 3: f = 0, abortThreshold = 1
    - n = 5, t = 4: f = 1, abortThreshold = 2
    - n = 7, t = 5: f = 2, abortThreshold = 3 -/
def ThresholdConfig.abortThreshold (cfg : ThresholdConfig) : Nat :=
  cfg.maxFaulty + 1

/-- Abort threshold is always positive. -/
theorem ThresholdConfig.abortThreshold_pos (cfg : ThresholdConfig) :
    cfg.abortThreshold ≥ 1 := by
  simp only [abortThreshold, maxFaulty]
  omega

/-- Abort threshold never exceeds total parties (when threshold is positive). -/
theorem ThresholdConfig.abortThreshold_le (cfg : ThresholdConfig)
    (h_pos : cfg.threshold ≥ 1) :
    cfg.abortThreshold ≤ cfg.totalParties := by
  simp only [abortThreshold, maxFaulty]
  have h := cfg.threshold_le_total
  omega

/-- Whether the threshold provides strict majority (t > n/2) -/
def ThresholdConfig.hasStrictMajority (cfg : ThresholdConfig) : Bool :=
  cfg.threshold * 2 > cfg.totalParties

/-- Whether the threshold provides 2/3 majority (t > 2n/3) -/
def ThresholdConfig.hasTwoThirdsMajority (cfg : ThresholdConfig) : Bool :=
  cfg.threshold * 3 > cfg.totalParties * 2

/-- Expected number of local rejection attempts based on bounds.
    Approximates 1 / (1 - 2·localBound/globalBound). -/
def ThresholdConfig.expectedLocalAttempts (cfg : ThresholdConfig) : Nat :=
  if cfg.globalBound > 2 * cfg.localBound then
    cfg.globalBound / (cfg.globalBound - 2 * cfg.localBound)
  else
    cfg.maxLocalAttempts  -- Fallback if bounds are tight

/-!
## Configuration Validation
-/

/-- Validation result with specific failure reason -/
inductive ConfigValidation
  | ok
  | noParties
  | thresholdZero
  | thresholdExceedsParties (t n : Nat)
  | maxSignersBelowThreshold (maxSigners t : Nat)
  | globalBoundZero
  | localBoundZero
  | localBoundTooLarge (localBd globalBd : Nat)
  deriving DecidableEq, Repr

/-- Validate a threshold configuration -/
def ThresholdConfig.validate (cfg : ThresholdConfig) : ConfigValidation :=
  if cfg.totalParties = 0 then .noParties
  else if cfg.threshold = 0 then .thresholdZero
  else if cfg.threshold > cfg.totalParties then
    .thresholdExceedsParties cfg.threshold cfg.totalParties
  else if cfg.maxSigners < cfg.threshold then
    .maxSignersBelowThreshold cfg.maxSigners cfg.threshold
  else if cfg.globalBound = 0 then .globalBoundZero
  else if cfg.localBound = 0 then .localBoundZero
  else if cfg.localBound * cfg.maxSigners > cfg.globalBound then
    .localBoundTooLarge cfg.localBound cfg.globalBound
  else .ok

/-- Check if configuration is valid (boolean version) -/
def ThresholdConfig.isValid (cfg : ThresholdConfig) : Bool :=
  cfg.validate = .ok

/-- ToString for ConfigValidation -/
instance : ToString ConfigValidation where
  toString
    | .ok => "configuration valid"
    | .noParties => "totalParties must be > 0"
    | .thresholdZero => "threshold must be > 0"
    | .thresholdExceedsParties t n => s!"threshold {t} exceeds totalParties {n}"
    | .maxSignersBelowThreshold m t => s!"maxSigners {m} below threshold {t}"
    | .globalBoundZero => "globalBound must be > 0"
    | .localBoundZero => "localBound is 0 (globalBound too small for maxSigners)"
    | .localBoundTooLarge l g => s!"localBound {l} exceeds globalBound {g}"

/-!
## Standard Configurations

Common configurations for different security levels and party counts.
-/

/-- Dilithium2 global bound: γ₁ - β = 2^17 - 78 = 131072 - 78 = 130994 -/
def dilithium2GlobalBound : Nat := 130994

/-- Dilithium3 global bound: γ₁ - β = 2^19 - 196 = 524288 - 196 = 524092 -/
def dilithium3GlobalBound : Nat := 524092

/-- Dilithium5 global bound: γ₁ - β = 2^19 - 120 = 524288 - 120 = 524168 -/
def dilithium5GlobalBound : Nat := 524168

/-- Create a Dilithium2-level configuration for n parties.
    Uses default 2/3+1 threshold. -/
def ThresholdConfig.dilithium2 (n : Nat) (hn : n > 0 := by omega) : ThresholdConfig :=
  ThresholdConfig.create n dilithium2GlobalBound
    (h1 := by simp only [defaultThreshold]; omega)
    (h3 := Nat.div_mul_le_self _ _)

/-- Create a Dilithium3-level configuration for n parties.
    Uses default 2/3+1 threshold. -/
def ThresholdConfig.dilithium3 (n : Nat) (hn : n > 0 := by omega) : ThresholdConfig :=
  ThresholdConfig.create n dilithium3GlobalBound
    (h1 := by simp only [defaultThreshold]; omega)
    (h3 := Nat.div_mul_le_self _ _)

/-- Create a Dilithium5-level configuration for n parties.
    Uses default 2/3+1 threshold. -/
def ThresholdConfig.dilithium5 (n : Nat) (hn : n > 0 := by omega) : ThresholdConfig :=
  ThresholdConfig.create n dilithium5GlobalBound
    (h1 := by simp only [defaultThreshold]; omega)
    (h3 := Nat.div_mul_le_self _ _)

/-!
## Aggregate Bound Guarantee

The fundamental theorem that enables local rejection:
if each signer's share is within localBound, the aggregate is within globalBound.
-/

/-- The aggregate bound guarantee: T shares within localBound sum to within globalBound.

    This is the key theorem for local rejection correctness:
    - Each signer produces z_i with ‖z_i‖∞ ≤ localBound
    - Aggregate z = Σ z_i has ‖z‖∞ ≤ T · localBound ≤ globalBound

    Proof: By triangle inequality for ℓ∞ norm and the config invariant. -/
theorem aggregate_bound_guarantee (cfg : ThresholdConfig)
    (shareBounds : List Nat)
    (hlen : shareBounds.length ≤ cfg.maxSigners)
    (hbounds : ∀ b ∈ shareBounds, b ≤ cfg.localBound) :
    shareBounds.sum ≤ cfg.globalBound := by
  calc shareBounds.sum
      ≤ shareBounds.length * cfg.localBound := by
        induction shareBounds with
        | nil => simp
        | cons x xs ih =>
          simp only [List.sum_cons, List.length_cons]
          have hx : x ≤ cfg.localBound := hbounds x (List.mem_cons.mpr (Or.inl rfl))
          have hxs : ∀ b ∈ xs, b ≤ cfg.localBound := fun b hb =>
            hbounds b (List.mem_cons.mpr (Or.inr hb))
          have ih' := ih (by simp at hlen; omega) hxs
          calc x + xs.sum
              ≤ cfg.localBound + xs.length * cfg.localBound := by
                apply Nat.add_le_add hx ih'
            _ = (xs.length + 1) * cfg.localBound := by ring
            _ = (x :: xs).length * cfg.localBound := by simp
    _ ≤ cfg.maxSigners * cfg.localBound := by
        apply Nat.mul_le_mul_right
        exact hlen
    _ = cfg.localBound * cfg.maxSigners := by ring
    _ ≤ cfg.globalBound := cfg.local_global_bound

/-!
## Pretty Printing
-/

/-- ToString for ThresholdConfig -/
instance : ToString ThresholdConfig where
  toString cfg :=
    s!"ThresholdConfig(n={cfg.totalParties}, t={cfg.threshold}, T={cfg.maxSigners}, " ++
    s!"B_global={cfg.globalBound}, B_local={cfg.localBound})"

end IceNine.Protocol.ThresholdConfig
