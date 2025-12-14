/-
# Threshold Configuration Proofs

Lemmas about ThresholdConfig properties. These prove correctness of the
configuration parameters and the fundamental aggregate bound guarantee.

Separated from Protocol/Core/ThresholdConfig.lean to maintain protocol/proof separation.
-/

import IceNine.Protocol.Core.ThresholdConfig
import Mathlib

set_option autoImplicit false

namespace IceNine.Proofs.Correctness.ThresholdConfig

open IceNine.Protocol.ThresholdConfig

/-!
## Default Threshold Properties
-/

/-- Default threshold is at least 1 for any positive n. -/
theorem defaultThreshold_pos (n : Nat) (hn : n > 0) : defaultThreshold n ≥ 1 := by
  simp only [defaultThreshold]
  omega

/-- Default threshold never exceeds n (for n ≥ 1). -/
theorem defaultThreshold_le (n : Nat) (hn : n ≥ 1) : defaultThreshold n ≤ n := by
  simp only [defaultThreshold]
  omega

/-!
## Abort Threshold Properties
-/

/-- Abort threshold is always positive. -/
theorem abortThreshold_pos (cfg : Protocol.ThresholdConfig.ThresholdConfig) :
    cfg.abortThreshold ≥ 1 := by
  simp only [Protocol.ThresholdConfig.ThresholdConfig.abortThreshold,
             Protocol.ThresholdConfig.ThresholdConfig.maxFaulty]
  omega

/-- Abort threshold never exceeds total parties (when threshold is positive). -/
theorem abortThreshold_le (cfg : Protocol.ThresholdConfig.ThresholdConfig)
    (h_pos : cfg.threshold ≥ 1) :
    cfg.abortThreshold ≤ cfg.totalParties := by
  simp only [Protocol.ThresholdConfig.ThresholdConfig.abortThreshold,
             Protocol.ThresholdConfig.ThresholdConfig.maxFaulty]
  have h := cfg.threshold_le_total
  omega

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
theorem aggregate_bound_guarantee (cfg : Protocol.ThresholdConfig.ThresholdConfig)
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

end IceNine.Proofs.Correctness.ThresholdConfig
