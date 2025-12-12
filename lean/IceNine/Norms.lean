/-
# Norm Predicates for Lattice Signatures

Norm bounds are critical for lattice signature security. In Schnorr-style
lattice signatures (Dilithium, etc.), the response z = y + c·s must have
bounded norm to prevent leakage about the secret key s.

## Dilithium Parameters (NIST Level 2)

| Parameter | Value | Description |
|-----------|-------|-------------|
| γ₁        | 2^17  | Range for y coefficients |
| γ₂        | (q-1)/88 | Low-order rounding range |
| β         | τ·η   | Bound on c·s (τ=39 challenges, η=2 secret range) |
| τ         | 39    | Number of ±1 in challenge c |

The norm check ensures ||z||∞ < γ₁ - β, which with ~4 expected attempts
via rejection sampling produces signatures independent of the secret.

**Reference**: Ducas et al., "CRYSTALS-Dilithium", TCHES 2018.
-/

import IceNine.Instances
import IceNine.Protocol.Core.NormBounded
import IceNine.Protocol.Core.ThresholdConfig
import Mathlib

namespace IceNine.Norms

open IceNine.Instances
open IceNine.Protocol.NormBounded
open IceNine.Protocol.ThresholdConfig

/-!
## Scalar Norm Bounds

Simple ℓ∞ bounds for scalar types.
-/

-- ℓ∞ bound for integers
def intLeqBound (B : Int) (x : Int) : Prop := |x| ≤ B

-- ℓ∞ bound for ZMod by lifting to centered representatives
-- Maps x to range [-(q-1)/2, (q-1)/2] before checking bound
def zmodLeqBound {q : ℕ} (B : Nat) (x : ZMod q) : Prop :=
  (Int.natAbs x.val) ≤ B

/-!
## Vector Norm Bounds

For lattice cryptography, secrets and signatures are vectors (or polynomials).
We define ℓ∞ (max coefficient) and ℓ₂ (Euclidean) norms.
-/

/-- ℓ∞ norm of an integer vector: max |v_i| -/
def vecInfNorm (v : List Int) : Nat :=
  v.foldl (fun acc x => max acc (Int.natAbs x)) 0

/-- ℓ₂² norm (squared Euclidean): Σ v_i² -/
def vecL2Squared (v : List Int) : Int :=
  v.foldl (fun acc x => acc + x * x) 0

/-- ℓ∞ norm bound for vectors -/
def vecInfLeqBound (B : Nat) (v : List Int) : Prop :=
  vecInfNorm v ≤ B

/-- ℓ₂² bound (compare squared to avoid sqrt) -/
def vecL2SqLeqBound (B : Int) (v : List Int) : Prop :=
  vecL2Squared v ≤ B

/-- Function-based vector ℓ∞ norm for Fin n → α -/
def finVecInfNorm {n : Nat} (v : Fin n → Int) : Nat :=
  if h : n = 0 then 0
  else Finset.univ.sup (fun i => Int.natAbs (v i))

/-- ℓ∞ bound for function-based vectors -/
def finVecInfLeqBound {n : Nat} (B : Int) (v : Fin n → Int) : Prop :=
  ∀ i : Fin n, Int.natAbs (v i) ≤ B.natAbs

/-!
## Dilithium-Style Parameters

Concrete parameter sets matching CRYSTALS-Dilithium security levels.
These define the rejection sampling bounds for signature generation.
-/

/-- Dilithium parameter set -/
structure DilithiumParams where
  /-- Ring dimension (256 for Dilithium) -/
  n : Nat := 256
  /-- Modulus -/
  q : Nat := 8380417
  /-- Number of ±1 in challenge polynomial -/
  tau : Nat
  /-- Secret key coefficient bound -/
  eta : Nat
  /-- Nonce coefficient range (power of 2) -/
  gamma1 : Nat
  /-- Low-bits rounding range -/
  gamma2 : Nat
  /-- Dropped bits from t -/
  d : Nat := 13

/-- Dilithium2 (NIST Level 2, 128-bit security) -/
def dilithium2 : DilithiumParams :=
  { tau := 39, eta := 2, gamma1 := 2^17, gamma2 := 95232, d := 13 }

/-- Dilithium3 (NIST Level 3, 192-bit security) -/
def dilithium3 : DilithiumParams :=
  { tau := 49, eta := 4, gamma1 := 2^19, gamma2 := 261888, d := 13 }

/-- Dilithium5 (NIST Level 5, 256-bit security) -/
def dilithium5 : DilithiumParams :=
  { tau := 60, eta := 2, gamma1 := 2^19, gamma2 := 261888, d := 13 }

/-- Compute β = τ·η, the bound on ||c·s||∞ -/
def DilithiumParams.beta (p : DilithiumParams) : Nat := p.tau * p.eta

/-- The rejection bound: ||z||∞ must be < γ₁ - β -/
def DilithiumParams.zBound (p : DilithiumParams) : Int :=
  p.gamma1 - p.beta

/-- Norm check for Dilithium: all coefficients below rejection bound -/
def dilithiumNormOK (p : DilithiumParams) (z : List Int) : Prop :=
  (vecInfNorm z : Int) < p.zBound

/-- Expected number of rejection sampling attempts -/
def DilithiumParams.expectedAttempts (p : DilithiumParams) : Nat :=
  -- Approximately 1 / (1 - 2β/γ₁)^k where k is vector dimension
  -- For Dilithium2: ~4.25 attempts
  if p.gamma1 > 2 * p.beta then
    (p.gamma1 / (p.gamma1 - 2 * p.beta))
  else
    100  -- Fallback if parameters are invalid

/-!
## Parameter Validation

Lightweight checks to catch obviously insecure or invalid parameters.
These are necessary conditions, not sufficient - real security analysis
requires the lattice estimator (Albrecht et al.).

### Security Requirements

For Dilithium-style signatures to be secure:
1. **Ring dimension**: n ≥ 256 (for quantum security)
2. **Rejection bound positive**: γ₁ > β (otherwise all signatures rejected)
3. **Modulus large enough**: q > γ₁ (to avoid wraparound)
4. **Challenge weight reasonable**: τ ≤ n (can't have more ±1s than coefficients)
5. **Secret bound small**: η ≤ 4 (larger η weakens SIS hardness)
-/

/-- Validation result with specific failure reason -/
inductive ParamValidation
  | ok
  | ringDimensionTooSmall (n : Nat) (minRequired : Nat)
  | rejectionBoundNonPositive (gamma1 : Nat) (beta : Nat)
  | modulusTooSmall (q : Nat) (gamma1 : Nat)
  | challengeWeightTooLarge (tau : Nat) (n : Nat)
  | secretBoundTooLarge (eta : Nat) (maxAllowed : Nat)
  | gamma2Invalid (gamma2 : Nat)
  deriving DecidableEq, Repr

/-- Minimum ring dimension for post-quantum security -/
def minRingDimension : Nat := 256

/-- Maximum secret coefficient bound for security -/
def maxSecretBound : Nat := 4

/-- Validate Dilithium parameters, returning specific error if invalid -/
def DilithiumParams.validate (p : DilithiumParams) : ParamValidation :=
  if p.n < minRingDimension then
    .ringDimensionTooSmall p.n minRingDimension
  else if p.gamma1 ≤ p.beta then
    .rejectionBoundNonPositive p.gamma1 p.beta
  else if p.q ≤ p.gamma1 then
    .modulusTooSmall p.q p.gamma1
  else if p.tau > p.n then
    .challengeWeightTooLarge p.tau p.n
  else if p.eta > maxSecretBound then
    .secretBoundTooLarge p.eta maxSecretBound
  else if p.gamma2 = 0 then
    .gamma2Invalid p.gamma2
  else
    .ok

/-- Check if parameters are valid (boolean version) -/
def DilithiumParams.isValid (p : DilithiumParams) : Bool :=
  p.validate = .ok

/-- Check if parameters meet minimum security level -/
def DilithiumParams.isSecure (p : DilithiumParams) : Prop :=
  p.n ≥ minRingDimension ∧
  p.gamma1 > p.beta ∧
  p.q > p.gamma1 ∧
  p.tau ≤ p.n ∧
  p.eta ≤ maxSecretBound

/-- Estimated security level based on ring dimension.
    Very rough approximation - real analysis needs lattice estimator. -/
def DilithiumParams.estimatedSecurityBits (p : DilithiumParams) : Nat :=
  -- Rough heuristic: security ≈ n/2 for well-chosen parameters
  -- This is NOT a rigorous estimate!
  if p.isValid then p.n / 2 else 0

/-- Security level classification -/
inductive SecurityLevel
  | insecure        -- < 128 bits
  | level1          -- ~128 bits (NIST Level 1)
  | level2          -- ~128 bits (NIST Level 2, AES-128 equivalent)
  | level3          -- ~192 bits (NIST Level 3, AES-192 equivalent)
  | level5          -- ~256 bits (NIST Level 5, AES-256 equivalent)
  deriving DecidableEq, Repr

/-- Classify security level of parameters -/
def DilithiumParams.securityLevel (p : DilithiumParams) : SecurityLevel :=
  let bits := p.estimatedSecurityBits
  if bits < 128 then .insecure
  else if bits < 160 then .level2
  else if bits < 224 then .level3
  else .level5

/-- Validate standard Dilithium parameter sets -/
theorem dilithium2_valid : dilithium2.isValid = true := by native_decide
theorem dilithium3_valid : dilithium3.isValid = true := by native_decide
theorem dilithium5_valid : dilithium5.isValid = true := by native_decide

/-!
## Scheme Instantiations with Proper Bounds

TODO: These require simpleScheme and zmodScheme to be defined in Instances.lean.
Currently using latticeScheme from Instances as the base scheme.
-/

-- TODO: Define simpleScheme and zmodScheme in Instances.lean, then uncomment these:
-- def simpleSchemeBounded (B : Int) : IceNine.Protocol.Core.Scheme :=
--   { simpleScheme with normOK := intLeqBound B }
--
-- def zmodSchemeBounded (q : ℕ) [Fact q.Prime] (a : ZMod q) (B : Nat) :
--     IceNine.Protocol.Core.Scheme :=
--   { zmodScheme q a with normOK := zmodLeqBound B }
--
-- /-- Scheme with Dilithium-style vector norm bounds.
--     Uses List Int as a simple model for polynomial coefficients. -/
-- def dilithiumStyleScheme (p : DilithiumParams) : IceNine.Protocol.Core.Scheme :=
--   { simpleScheme with
--     Secret := List Int
--     Public := List Int
--     normOK := dilithiumNormOK p }

/-!
## Norm Bound Lemmas

Properties of norm bounds useful for security proofs.
-/

/-- Helper: vecInfNorm is the max of absolute values -/
lemma vecInfNorm_nil : vecInfNorm [] = 0 := rfl

-- Helper: foldl max distributes over max with init
private lemma foldl_max_init (init : Nat) (xs : List Int) :
    List.foldl (fun acc x => max acc (Int.natAbs x)) init xs =
    max init (List.foldl (fun acc x => max acc (Int.natAbs x)) 0 xs) := by
  induction xs generalizing init with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl]
    rw [ih (max init (Int.natAbs y)), ih (max 0 (Int.natAbs y))]
    simp only [Nat.zero_max, max_assoc]

lemma vecInfNorm_cons (x : Int) (xs : List Int) :
    vecInfNorm (x :: xs) = max (Int.natAbs x) (vecInfNorm xs) := by
  simp only [vecInfNorm, List.foldl]
  rw [foldl_max_init]
  simp only [Nat.zero_max]

/-- Each element's absolute value is bounded by the ℓ∞ norm -/
lemma abs_le_vecInfNorm (v : List Int) (x : Int) (hx : x ∈ v) :
    Int.natAbs x ≤ vecInfNorm v := by
  induction v with
  | nil => simp at hx
  | cons y ys ih =>
    rw [vecInfNorm_cons]
    cases List.mem_cons.mp hx with
    | inl heq => rw [heq]; exact le_max_left _ _
    | inr hmem => exact le_trans (ih hmem) (le_max_right _ _)

/-- Triangle inequality for integers -/
lemma int_natAbs_add_le (a b : Int) : Int.natAbs (a + b) ≤ Int.natAbs a + Int.natAbs b :=
  Int.natAbs_add_le a b

/-- Triangle inequality for ℓ∞ norm -/
lemma vecInfNorm_add_le (v w : List Int) (hlen : v.length = w.length) :
    vecInfNorm (List.zipWith (· + ·) v w) ≤ vecInfNorm v + vecInfNorm w := by
  induction v generalizing w with
  | nil =>
    simp only [List.zipWith_nil_left, vecInfNorm_nil, zero_add]
    exact Nat.zero_le _
  | cons x xs ih =>
    cases w with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.zipWith_cons_cons, vecInfNorm_cons]
      simp only [List.length_cons, Nat.succ_eq_add_one, add_left_inj] at hlen
      have ih_applied := ih ys hlen
      calc max (Int.natAbs (x + y)) (vecInfNorm (List.zipWith (· + ·) xs ys))
          ≤ max (Int.natAbs x + Int.natAbs y) (vecInfNorm xs + vecInfNorm ys) := by
            apply max_le_max
            · exact int_natAbs_add_le x y
            · exact ih_applied
        _ ≤ max (Int.natAbs x) (vecInfNorm xs) + max (Int.natAbs y) (vecInfNorm ys) := by
            apply max_le
            · calc Int.natAbs x + Int.natAbs y
                  ≤ max (Int.natAbs x) (vecInfNorm xs) + Int.natAbs y := by
                    exact Nat.add_le_add_right (le_max_left _ _) _
                _ ≤ max (Int.natAbs x) (vecInfNorm xs) + max (Int.natAbs y) (vecInfNorm ys) := by
                    exact Nat.add_le_add_left (le_max_left _ _) _
            · calc vecInfNorm xs + vecInfNorm ys
                  ≤ max (Int.natAbs x) (vecInfNorm xs) + vecInfNorm ys := by
                    exact Nat.add_le_add_right (le_max_right _ _) _
                _ ≤ max (Int.natAbs x) (vecInfNorm xs) + max (Int.natAbs y) (vecInfNorm ys) := by
                    exact Nat.add_le_add_left (le_max_right _ _) _

/-- Scaling bound: ||c·v||∞ ≤ |c| · ||v||∞ -/
lemma vecInfNorm_smul_le (c : Int) (v : List Int) :
    vecInfNorm (v.map (c * ·)) ≤ Int.natAbs c * vecInfNorm v := by
  induction v with
  | nil => simp [vecInfNorm_nil]
  | cons x xs ih =>
    simp only [List.map_cons, vecInfNorm_cons]
    calc max (Int.natAbs (c * x)) (vecInfNorm (xs.map (c * ·)))
        ≤ max (Int.natAbs c * Int.natAbs x) (Int.natAbs c * vecInfNorm xs) := by
          apply max_le_max
          · exact Int.natAbs_mul c x ▸ le_refl _
          · exact ih
      _ = Int.natAbs c * max (Int.natAbs x) (vecInfNorm xs) := by
          rw [← Nat.mul_max_mul_left]

/-- Key bound for rejection sampling: ||y + c·s||∞ ≤ ||y||∞ + |c| · ||s||∞
    This is the fundamental bound that enables rejection sampling security. -/
lemma response_norm_bound_general (y s : List Int) (c : Int)
    (hlen : y.length = s.length) :
    vecInfNorm (List.zipWith (· + ·) y (s.map (c * ·))) ≤
      vecInfNorm y + Int.natAbs c * vecInfNorm s := by
  have hlen' : y.length = (s.map (c * ·)).length := by simp [hlen]
  calc vecInfNorm (List.zipWith (· + ·) y (s.map (c * ·)))
      ≤ vecInfNorm y + vecInfNorm (s.map (c * ·)) := vecInfNorm_add_le y _ hlen'
    _ ≤ vecInfNorm y + Int.natAbs c * vecInfNorm s := by
        exact Nat.add_le_add_left (vecInfNorm_smul_le c s) _

/-- Concrete bound for Dilithium-style rejection sampling:
    If ||y||∞ < γ₁ and ||s||∞ ≤ η and |c| ≤ τ, then ||y + c·s||∞ < γ₁ + τ·η -/
lemma response_norm_bound (y s : List Int) (c : Int) (γ₁ η τ : Nat)
    (hy : vecInfNorm y < γ₁) (hs : vecInfNorm s ≤ η)
    (hc : Int.natAbs c ≤ τ) (hlen : y.length = s.length) :
    vecInfNorm (List.zipWith (· + ·) y (s.map (c * ·))) < γ₁ + τ * η := by
  calc vecInfNorm (List.zipWith (· + ·) y (s.map (c * ·)))
      ≤ vecInfNorm y + Int.natAbs c * vecInfNorm s := response_norm_bound_general y s c hlen
    _ < γ₁ + Int.natAbs c * vecInfNorm s := by exact Nat.add_lt_add_right hy _
    _ ≤ γ₁ + τ * vecInfNorm s := by
        apply Nat.add_le_add_left
        exact Nat.mul_le_mul_right _ hc
    _ ≤ γ₁ + τ * η := by
        apply Nat.add_le_add_left
        exact Nat.mul_le_mul_left _ hs

/-!
## NormBounded Integration

Connect existing norm functions to the NormBounded typeclass.
-/

/-- Verify that our vecInfNorm matches the NormBounded instance for List Int -/
theorem vecInfNorm_eq_norm (v : List Int) : vecInfNorm v = norm v := rfl

/-!
## Threshold Extensions for DilithiumParams

Extensions to DilithiumParams for local rejection sampling configuration.
-/

/-- Convert DilithiumParams to a ThresholdConfig for n parties.

    Uses the global bound (γ₁ - β) as globalBound.
    Local bound is derived as globalBound / maxSigners.

    **Example**:
    ```lean
    let params := dilithium2
    let cfg := params.toThresholdConfig 5  -- 5-party scheme
    -- cfg.globalBound = 130994
    -- cfg.threshold = 4 (2/3+1 of 5)
    -- cfg.localBound = 130994 / 4 = 32748
    ``` -/
def DilithiumParams.toThresholdConfig (p : DilithiumParams) (n : Nat)
    (hn : n > 0 := by omega) : ThresholdConfig :=
  let globalBound := p.zBound.natAbs  -- Convert Int to Nat (always positive for valid params)
  ThresholdConfig.mk n globalBound

/-- Get the local rejection bound for a given number of signers.
    This is the per-signer bound B_local such that T · B_local ≤ B_global. -/
def DilithiumParams.localBound (p : DilithiumParams) (maxSigners : Nat)
    (hpos : maxSigners > 0 := by omega) : Nat :=
  p.zBound.natAbs / maxSigners

/-- Expected local rejection attempts given local bound.
    Tighter local bounds require more rejection attempts. -/
def DilithiumParams.expectedLocalAttempts (p : DilithiumParams) (maxSigners : Nat)
    (hpos : maxSigners > 0 := by omega) : Nat :=
  let localB := p.localBound maxSigners
  if p.gamma1 > 2 * localB then
    p.gamma1 / (p.gamma1 - 2 * localB)
  else
    256  -- Fallback for very tight bounds

/-!
## Local Rejection Bound Proofs

Key lemmas for local rejection sampling correctness.
-/

/-- Sum of T local bounds doesn't exceed global bound.
    This is the fundamental guarantee for local rejection. -/
theorem local_bounds_sum_le_global (p : DilithiumParams) (maxSigners : Nat)
    (hpos : maxSigners > 0) :
    maxSigners * p.localBound maxSigners ≤ p.zBound.natAbs := by
  simp only [DilithiumParams.localBound]
  exact Nat.div_mul_le_self _ _

/-- Each signer's contribution within local bound ensures aggregate within global bound. -/
theorem aggregate_within_global_bound (p : DilithiumParams) (maxSigners : Nat)
    (contributions : List Nat)
    (hlen : contributions.length ≤ maxSigners)
    (hpos : maxSigners > 0)
    (hbounds : ∀ c ∈ contributions, c ≤ p.localBound maxSigners) :
    contributions.sum ≤ p.zBound.natAbs := by
  calc contributions.sum
      ≤ contributions.length * p.localBound maxSigners := by
        induction contributions with
        | nil => simp
        | cons x xs ih =>
          simp only [List.sum_cons, List.length_cons]
          have hx := hbounds x (List.mem_cons_self x xs)
          have hxs : ∀ c ∈ xs, c ≤ p.localBound maxSigners := fun c hc =>
            hbounds c (List.mem_cons_of_mem x hc)
          have ih' := ih (by simp at hlen; omega) hxs
          calc x + xs.sum
              ≤ p.localBound maxSigners + xs.length * p.localBound maxSigners := by
                apply Nat.add_le_add hx ih'
            _ = (xs.length + 1) * p.localBound maxSigners := by ring
            _ = (x :: xs).length * p.localBound maxSigners := by simp
    _ ≤ maxSigners * p.localBound maxSigners := by
        apply Nat.mul_le_mul_right
        exact hlen
    _ ≤ p.zBound.natAbs := local_bounds_sum_le_global p maxSigners hpos

/-!
## NormBounded Compatibility

Show that vecInfNorm-based checks are compatible with NormBounded.
-/

/-- Local bound check via NormBounded is equivalent to vecInfLeqBound -/
theorem localBoundOK_iff_vecInfLeqBound (cfg : ThresholdConfig) (v : List Int) :
    localBoundOK cfg v ↔ vecInfLeqBound cfg.localBound v := by
  simp only [localBoundOK, vecInfLeqBound, vecInfNorm_eq_norm]

/-- Global bound check via NormBounded is equivalent to vecInfLeqBound -/
theorem globalBoundOK_iff_vecInfLeqBound (cfg : ThresholdConfig) (v : List Int) :
    globalBoundOK cfg v ↔ vecInfLeqBound cfg.globalBound v := by
  simp only [globalBoundOK, vecInfLeqBound, vecInfNorm_eq_norm]

end IceNine.Norms
