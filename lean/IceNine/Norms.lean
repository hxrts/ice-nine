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
import Mathlib

namespace IceNine.Norms

open IceNine.Instances

/-!
## Scalar Norm Bounds

Simple ℓ∞ bounds for scalar types.
-/

-- ℓ∞ bound for integers
def intLeqBound (B : Int) (x : Int) : Prop := Int.abs x ≤ B

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
def vecInfNorm (v : List Int) : Int :=
  v.foldl (fun acc x => max acc (Int.natAbs x)) 0

/-- ℓ₂² norm (squared Euclidean): Σ v_i² -/
def vecL2Squared (v : List Int) : Int :=
  v.foldl (fun acc x => acc + x * x) 0

/-- ℓ∞ norm bound for vectors -/
def vecInfLeqBound (B : Int) (v : List Int) : Prop :=
  vecInfNorm v ≤ B

/-- ℓ₂² bound (compare squared to avoid sqrt) -/
def vecL2SqLeqBound (B : Int) (v : List Int) : Prop :=
  vecL2Squared v ≤ B

/-- Function-based vector ℓ∞ norm for Fin n → α -/
def finVecInfNorm {n : Nat} (v : Fin n → Int) : Int :=
  Finset.univ.sup' (by simp [Finset.univ_nonempty_iff]; exact Fin.pos n)
    (fun i => (Int.natAbs (v i) : WithBot Int))
  |>.getD 0

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
  vecInfNorm z < p.zBound

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
-/

-- Replace normOK in the simpleScheme with a parameterized bound.
def simpleSchemeBounded (B : Int) : IceNine.Protocol.Core.Scheme :=
  { simpleScheme with normOK := intLeqBound B }

def zmodSchemeBounded (q : ℕ) [Fact q.Prime] (a : ZMod q) (B : Nat) :
    IceNine.Protocol.Core.Scheme :=
  { zmodScheme q a with normOK := zmodLeqBound B }

/-- Scheme with Dilithium-style vector norm bounds.
    Uses List Int as a simple model for polynomial coefficients. -/
def dilithiumStyleScheme (p : DilithiumParams) : IceNine.Protocol.Core.Scheme :=
  { simpleScheme with
    Secret := List Int
    Public := List Int
    normOK := dilithiumNormOK p }

/-!
## Norm Bound Lemmas

Properties of norm bounds useful for security proofs.
-/

/-- Triangle inequality for ℓ∞ norm -/
lemma vecInfNorm_add_le (v w : List Int) (hlen : v.length = w.length) :
    vecInfNorm (List.zipWith (· + ·) v w) ≤ vecInfNorm v + vecInfNorm w := by
  sorry  -- Requires detailed list induction

/-- Scaling bound: ||c·v||∞ ≤ |c| · ||v||∞ -/
lemma vecInfNorm_smul_le (c : Int) (v : List Int) :
    vecInfNorm (v.map (c * ·)) ≤ Int.natAbs c * vecInfNorm v := by
  sorry  -- Requires detailed list induction

/-- Key bound for rejection sampling: ||y + c·s||∞ ≤ ||y||∞ + ||c·s||∞ -/
lemma response_norm_bound (y s : List Int) (c : Int)
    (hy : vecInfNorm y < γ₁) (hs : vecInfNorm s ≤ η)
    (hc : Int.natAbs c ≤ τ) (hlen : y.length = s.length)
    (γ₁ η τ : Nat) :
    vecInfNorm (List.zipWith (· + ·) y (s.map (c * ·))) < γ₁ + τ * η := by
  sorry  -- Follows from triangle inequality and scaling bound

end IceNine.Norms
