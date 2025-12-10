/-
# Security Assumptions

Abstract security assumptions for threshold signature proofs, stated in a
post-quantum setting. We expose a small catalog of NIST PQC (Dilithium-style)
parameter sets via `PQSecurityLevel` (L1/L3/L5) and a helper
`mkLatticeAssumptions` that constructs the assumption bundle from that level.
In practice you choose a level and provide the scheme-specific hardness claims
(`hashQROM`, `commitPQBinding`, `normLeakageBound`, and corruption bound).
- Quantum Random Oracle model (QROM) for the hash function
- Commitment binding against quantum adversaries
- Norm bounds for lattice security (SIS/MLWE hardness)
- Corruption bounds for threshold security

All security theorems are parameterized by these assumptions.

## Lattice Hardness Problems

The security of lattice-based signatures reduces to two computational problems:

### Short Integer Solution (SIS)
Given A ∈ Z_q^{n×m}, find z ∈ Z^m with ||z|| ≤ β and Az = 0 mod q.
Hardness: For appropriate parameters, as hard as worst-case lattice problems.

**Reference**: Ajtai, "Generating Hard Instances of Lattice Problems", STOC 1996.

### Module Learning With Errors (MLWE)
Distinguish (A, As + e) from (A, u) where A is uniform, s,e are small.
This generalizes Ring-LWE to module lattices for flexible security/efficiency.

**Reference**: Langlois & Stehlé, "Worst-case to Average-case Reductions
for Module Lattices", Designs, Codes and Cryptography, 2015.
-/

import IceNine.Protocol.Core
import IceNine.Protocol.Sign
import IceNine.Protocol.DKGCore
import Mathlib

namespace IceNine.Security

open IceNine.Protocol

/-!
## Short Integer Solution (SIS) Problem

SIS is the foundation for lattice signature unforgeability.
Finding a forgery ≈ finding a short vector in the kernel of A.
-/

/-- SIS problem parameters -/
structure SISParams where
  /-- Lattice dimension (rows of A) -/
  n : Nat
  /-- Number of columns of A -/
  m : Nat
  /-- Modulus -/
  q : Nat
  /-- Solution norm bound -/
  beta : Nat
  /-- Security requirement: m > n log q for meaningful hardness -/
  m_large : m > n * Nat.log2 q := by decide

/-- SIS problem instance: public matrix A -/
structure SISInstance (p : SISParams) where
  /-- Public matrix A ∈ Z_q^{n×m} -/
  A : Fin p.n → Fin p.m → ZMod p.q

/-- A solution to SIS: short vector z with Az = 0 -/
structure SISSolution (p : SISParams) (inst : SISInstance p) where
  /-- Solution vector z ∈ Z^m -/
  z : Fin p.m → Int
  /-- z is short: ||z||∞ ≤ β -/
  z_short : ∀ i, Int.natAbs (z i) ≤ p.beta
  /-- z is nonzero -/
  z_nonzero : ∃ i, z i ≠ 0
  /-- Az = 0 mod q -/
  Az_zero : ∀ i : Fin p.n,
    (Finset.univ.sum fun j => inst.A i j * (z j : ZMod p.q)) = 0

/-- SIS hardness assumption: no efficient algorithm finds solutions -/
def SISHard (p : SISParams) : Prop :=
  -- Axiomatized: for random A, finding SISSolution is computationally infeasible
  True

/-- NIST PQC (Dilithium2-ish) SIS parameters, Level 1 (~128-bit) -/
def sisL1 : SISParams :=
  { n := 256, m := 512, q := 8380417, beta := 78
    m_large := by native_decide }

/-- NIST PQC (Dilithium3-ish) SIS parameters, Level 3 (~192-bit) -/
def sisL3 : SISParams :=
  { n := 256, m := 512, q := 8380417, beta := 120
    m_large := by native_decide }

/-- NIST PQC (Dilithium5-ish) SIS parameters, Level 5 (~256-bit) -/
def sisL5 : SISParams :=
  { n := 256, m := 512, q := 8380417, beta := 196
    m_large := by native_decide }

/-!
## Module Learning With Errors (MLWE) Problem

MLWE underlies key secrecy: recovering the secret key from
public key requires solving MLWE.
-/

/-- MLWE problem parameters -/
structure MLWEParams where
  /-- Ring dimension (degree of polynomial ring R_q = Z_q[X]/(X^n + 1)) -/
  n : Nat
  /-- Module rank (number of ring elements in secret) -/
  k : Nat
  /-- Modulus -/
  q : Nat
  /-- Error distribution parameter (std dev for Gaussian, bound for uniform) -/
  eta : Nat

/-- MLWE instance: public (A, b = As + e) -/
structure MLWEInstance (p : MLWEParams) where
  /-- Public matrix A ∈ R_q^{k×k} (k×k matrix of polynomials) -/
  A : Fin p.k → Fin p.k → (Fin p.n → ZMod p.q)
  /-- Public vector b = As + e ∈ R_q^k -/
  b : Fin p.k → (Fin p.n → ZMod p.q)

/-- MLWE secret and error -/
structure MLWESecret (p : MLWEParams) where
  /-- Secret vector s ∈ R_q^k with small coefficients -/
  s : Fin p.k → (Fin p.n → Int)
  /-- Error vector e ∈ R_q^k with small coefficients -/
  e : Fin p.k → (Fin p.n → Int)
  /-- s is short -/
  s_short : ∀ i j, Int.natAbs (s i j) ≤ p.eta
  /-- e is short -/
  e_short : ∀ i j, Int.natAbs (e i j) ≤ p.eta

/-- MLWE hardness: distinguishing (A, As+e) from (A, u) is hard -/
def MLWEHard (p : MLWEParams) : Prop :=
  -- Axiomatized: (A, As+e) computationally indistinguishable from (A, uniform)
  True

/-- Ring-LWE is MLWE with k=1 (single polynomial) -/
def RLWEParams (n q eta : Nat) : MLWEParams :=
  { n := n, k := 1, q := q, eta := eta }

/-- NIST PQC (Dilithium2) MLWE parameters, Level 1 (~128-bit) -/
def mlweL1 : MLWEParams :=
  { n := 256, k := 4, q := 8380417, eta := 2 }

/-- NIST PQC (Dilithium3) MLWE parameters, Level 3 (~192-bit) -/
def mlweL3 : MLWEParams :=
  { n := 256, k := 6, q := 8380417, eta := 4 }

/-- NIST PQC (Dilithium5) MLWE parameters, Level 5 (~256-bit) -/
def mlweL5 : MLWEParams :=
  { n := 256, k := 8, q := 8380417, eta := 4 }

/-- Security levels aligned with NIST PQC Dilithium parameter sets. -/
inductive PQSecurityLevel
  | L1 | L3 | L5
  deriving DecidableEq, Repr

/-- Pick SIS params by security level. -/
def sisParamsOfLevel : PQSecurityLevel → SISParams
  | .L1 => sisL1
  | .L3 => sisL3
  | .L5 => sisL5

/-- Pick MLWE params by security level. -/
def mlweParamsOfLevel : PQSecurityLevel → MLWEParams
  | .L1 => mlweL1
  | .L3 => mlweL3
  | .L5 => mlweL5

/-- Instantiate lattice assumptions from a security level. -/
def mkLatticeAssumptions
  (S : Scheme)
  (lvl : PQSecurityLevel)
  (hashRO : Prop)
  (commitCR : Prop)
  (normLeakageBound : Prop)
  (corruptionBound : Nat)
  (sis_hard : SISHard (sisParamsOfLevel lvl))
  (mlwe_hard : MLWEHard (mlweParamsOfLevel lvl))
  : LatticeAssumptions S :=
{ hashRO := hashRO
  commitCR := commitCR
  normLeakageBound := normLeakageBound
  corruptionBound := corruptionBound
  sisParams := some (sisParamsOfLevel lvl)
  mlweParams := some (mlweParamsOfLevel lvl)
  sisInst := sisParamsOfLevel lvl
  mlweInst := mlweParamsOfLevel lvl
  sis_hard := sis_hard
  mlwe_hard := mlwe_hard }

/-- Default lattice assumptions for our concrete latticeScheme at Level 1.
    Hash/commit/norm bounds are treated axiomatically here (True). -/
def latticeAssumptionsL1 : LatticeAssumptions (IceNine.Instances.latticeScheme ()) :=
  mkLatticeAssumptions (S := IceNine.Instances.latticeScheme ()) PQSecurityLevel.L1
    True True True 0
    (by trivial) (by trivial)

/-!
## Rejection Sampling Model

The signing protocol uses rejection sampling to ensure responses don't leak
information about the secret key. We axiomatize the key properties since
probabilistic reasoning is not well-supported in Lean.

**Background**: In Dilithium-style signatures, the response z = y + c·s must be
independent of s. Rejection sampling achieves this by:
1. Sampling y from a wide distribution
2. Rejecting z if ||z||∞ ≥ γ₁ - β (where β = τ·η)
3. Accepted z values follow a distribution independent of s

**Reference**: Lyubashevsky, "Fiat-Shamir with Aborts", ASIACRYPT 2009.
-/

/-- Acceptance probability bound for rejection sampling.
    Guarantees signing terminates in expected O(κ) attempts.

    For Dilithium parameters, acceptance probability is approximately 1/4,
    so κ ≈ 4 expected iterations. -/
structure AcceptanceProbability (S : Scheme) where
  /-- Upper bound on expected number of rejection sampling iterations -/
  expectedIterations : Nat
  /-- Bound is valid (acceptance prob ≥ 1/κ) -/
  bound_valid : expectedIterations > 0
  /-- Axiom: honest parties with short secrets accept with this probability -/
  acceptance_rate : True  -- Axiomatized; depends on γ₁, β, secret distribution

/-- Response independence axiom for rejection sampling.
    This is THE key security property: accepted responses reveal nothing about s.

    Formally: For any two secrets s₁, s₂ with ||sᵢ||∞ ≤ η, the distributions
    {z : z = y + c·s₁, ||z||∞ < γ₁ - β} and {z : z = y + c·s₂, ||z||∞ < γ₁ - β}
    are statistically close.

    **NOT PROVABLE IN LEAN**: This requires probabilistic reasoning about
    distributions. We axiomatize it as the key security property that rejection
    sampling provides. -/
structure ResponseIndependence (S : Scheme) : Prop where
  /-- Accepted responses are independent of the secret key -/
  independence : True  -- Axiomatized; this is what rejection sampling achieves

/-- Standard Dilithium acceptance probability (≈ 1/4, so expect 4 iterations) -/
def dilithiumAcceptance (S : Scheme) : AcceptanceProbability S :=
  { expectedIterations := 4
    bound_valid := by decide
    acceptance_rate := True.intro }

/-!
## Security Reduction Structure

Documents how signature security reduces to SIS/MLWE hardness.
-/

/-- Reduction from signature forgery to SIS.
    If an adversary can forge signatures, we can solve SIS. -/
structure ForgerToSIS (S : Scheme) (p : SISParams) where
  /-- The forger's advantage (probability of forgery) -/
  forgerAdvantage : Real
  /-- Number of signing queries the forger makes -/
  signingQueries : Nat
  /-- Number of hash queries (random oracle) -/
  hashQueries : Nat
  /-- The resulting SIS solver's advantage -/
  sisAdvantage : Real
  /-- Reduction tightness: SIS advantage ≥ forger advantage / loss factor -/
  reduction_tight :
    sisAdvantage ≥ forgerAdvantage / (hashQueries * signingQueries)

/-- Reduction from key recovery to MLWE.
    If an adversary can recover secret key, we can solve MLWE. -/
structure KeyRecoveryToMLWE (S : Scheme) (p : MLWEParams) where
  /-- The key recovery advantage -/
  keyRecoveryAdvantage : Real
  /-- The resulting MLWE distinguisher's advantage -/
  mlweAdvantage : Real
  /-- Reduction is tight for key recovery -/
  reduction_tight : mlweAdvantage ≥ keyRecoveryAdvantage

/-!
## Collision Resistance

Hash-based commitments derive binding from collision resistance of the underlying
hash function. We axiomatize CR as a property that can be assumed for concrete
hash instantiations (SHA3, SHAKE, etc.).
-/

/-- Collision resistance assumption for a hash function.
    States that finding distinct inputs with the same output is computationally infeasible.

    For hash-based commitments Com(x, r) = H(x || r):
    - Binding follows from CR: if Com(x₁, r₁) = Com(x₂, r₂), then x₁ || r₁ = x₂ || r₂
    - This implies x₁ = x₂ (the binding property)

    **Reference**: Halevi & Micali, "Practical and Provably-Secure Commitment Schemes
    from Collision-Free Hashing", CRYPTO 1996. -/
structure CollisionResistant (H : α → β) : Prop where
  /-- No efficient algorithm can find x₁ ≠ x₂ with H(x₁) = H(x₂) -/
  no_collisions : True  -- Axiomatized; in practice, instantiate with concrete hash assumption

/-- Collision resistance for the scheme's commitment function.
    This is sufficient for binding: CR → Binding. -/
def commitmentCR (S : Scheme) : Prop :=
  -- The commitment function is collision resistant when viewed as H(x || opening)
  S.hashCollisionResistant

/-!
## Hiding Assumption

Hash-based commitments are NOT perfectly hiding. They provide computational hiding
under the Random Oracle Model (ROM). We explicitly axiomatize this assumption
since it cannot be proven from first principles.

**WARNING**: This is a stronger assumption than collision resistance. Protocols
that require hiding (e.g., for zero-knowledge properties) must explicitly include
this assumption in their security theorems.
-/

/-- Hiding assumption for commitments.
    States that Com(x₁, r) and Com(x₂, r') are computationally indistinguishable
    for random r, r'.

    For hash-based commitments, this requires the Random Oracle Model.
    For Pedersen commitments, this holds perfectly (information-theoretically).

    **NOT FORMALIZED**: We cannot prove hiding in Lean without probabilistic
    reasoning. This is an explicit axiom that must be assumed. -/
structure HidingAssumption (S : Scheme) : Prop where
  /-- Commitments reveal nothing about the committed value (ROM assumption) -/
  hiding : True  -- Axiomatized; requires ROM or DDH depending on instantiation

/-!
## Assumption Bundle

Packages all cryptographic assumptions needed for security proofs.
Concrete instantiations must prove these properties hold.
-/

/-- Security assumptions for threshold signature scheme. -/
structure Assumptions (S : Scheme) where
  /-- Hash behaves as a quantum random oracle (QROM) for Fiat-Shamir. -/
  hashRO            : Prop
  /-- Commitment scheme is collision resistant (implies binding). -/
  commitCR          : Prop := commitmentCR S
  /-- Commitment hiding (requires ROM; NOT formally proven). -/
  commitHiding      : HidingAssumption S := ⟨True.intro⟩
  /-- Norm bounds prevent leakage in lattice setting. -/
  normLeakageBound  : Prop
  /-- Max corrupted parties (must be < threshold for security). -/
  corruptionBound   : Nat
  /-- SIS parameters for unforgeability (post-quantum). -/
  sisParams : Option SISParams := none
  /-- MLWE parameters for key secrecy (post-quantum). -/
  mlweParams : Option MLWEParams := none

/-- Full lattice assumptions including SIS and MLWE -/
structure LatticeAssumptions (S : Scheme) extends Assumptions S where
  /-- SIS instance derived from scheme -/
  sisInst : SISParams
  /-- MLWE instance derived from scheme -/
  mlweInst : MLWEParams
  /-- SIS is hard for these parameters -/
  sis_hard : SISHard sisInst
  /-- MLWE is hard for these parameters -/
  mlwe_hard : MLWEHard mlweInst

/-!
## Security Theorems

Main security guarantees, parameterized by assumptions.
-/

/-- Threshold Unforgeability under Chosen Message Attack.
    Adversary can't forge signatures without ≥ threshold honest parties.

    Proof sketch (informal):
    1. Assume adversary A forges with advantage ε
    2. Build SIS solver B that uses A as subroutine
    3. B embeds SIS challenge into public key
    4. When A outputs forgery (m*, σ*), B extracts SIS solution
    5. By SIS hardness, ε must be negligible -/
def thresholdUFcma (S : Scheme) (A : Assumptions S) : Prop :=
  A.hashRO ∧ A.commitCR ∧ A.normLeakageBound

/-- Key secrecy: adversary learns nothing about secret shares.

    Proof sketch (informal):
    1. Public key pk = A·sk where sk is secret
    2. If adversary distinguishes sk from random, solve MLWE
    3. By MLWE hardness, pk reveals nothing about sk -/
def keySecrecy (S : Scheme) (A : LatticeAssumptions S) : Prop :=
  A.mlwe_hard

/-- Liveness: honest parties either complete signing or detect abort.
    No silent failures - either succeed or return error. -/
def livenessOrAbort (S : Scheme) (A : Assumptions S) : Prop := True

/-!
## Parameter Validation

Lightweight checks to catch obviously insecure or invalid parameters.
These are necessary conditions, not sufficient for security - real analysis
requires the lattice estimator tool (Albrecht et al., https://lattice-estimator.readthedocs.io/).

### SIS Security Requirements (soundness checks)

For SIS(n, m, q, β) to be hard (post-quantum):
1. n ≥ 256
2. m ≥ 2n
3. β < q/2
4. q prime or prime power

### MLWE Security Requirements (soundness checks)

For MLWE(n, k, q, η) to be hard:
1. n ≥ 256 and power of 2 (for NTT)
2. k ≥ 1 (k=1 = Ring-LWE; higher k improves security)
3. η small (typically ≤ 4)
4. q ≥ n and NTT-friendly (q ≡ 1 mod 2n)
-/

/-- Minimum dimension for 128-bit security against known lattice attacks -/
def minSecureDimension : Nat := 256

/-- SIS validation result with specific failure reason -/
inductive SISValidation
  | ok
  | dimensionTooSmall (n : Nat) (minRequired : Nat)
  | notEnoughColumns (m : Nat) (minRequired : Nat)
  | betaTooLarge (beta : Nat) (maxAllowed : Nat)
  | modulusTooSmall (q : Nat)
  deriving DecidableEq, Repr

/-- Validate SIS parameters, returning specific error if invalid -/
def SISParams.validate (p : SISParams) : SISValidation :=
  if p.n < minSecureDimension then
    .dimensionTooSmall p.n minSecureDimension
  else if p.m < 2 * p.n then
    .notEnoughColumns p.m (2 * p.n)
  else if p.beta ≥ p.q / 2 then
    .betaTooLarge p.beta (p.q / 2)
  else if p.q < 2 then
    .modulusTooSmall p.q
  else
    .ok

/-- Check if SIS parameters are valid (boolean) -/
def SISParams.isValid (p : SISParams) : Bool :=
  p.validate = .ok

/-- Check if SIS parameters are secure (Prop) -/
def SISParams.isSecure (p : SISParams) : Prop :=
  p.n ≥ minSecureDimension ∧
  p.m ≥ 2 * p.n ∧
  p.beta < p.q / 2

/-- MLWE validation result with specific failure reason -/
inductive MLWEValidation
  | ok
  | ringDimensionTooSmall (n : Nat) (minRequired : Nat)
  | ringDimensionNotPowerOf2 (n : Nat)
  | moduleRankTooSmall (k : Nat)
  | errorBoundTooLarge (eta : Nat) (maxAllowed : Nat)
  | modulusTooSmall (q : Nat)
  deriving DecidableEq, Repr

/-- Check if n is a power of 2 -/
def isPowerOf2 (n : Nat) : Bool :=
  n > 0 && (n &&& (n - 1)) = 0

/-- Validate MLWE parameters, returning specific error if invalid -/
def MLWEParams.validate (p : MLWEParams) : MLWEValidation :=
  if p.n < minSecureDimension then
    .ringDimensionTooSmall p.n minSecureDimension
  else if !isPowerOf2 p.n then
    .ringDimensionNotPowerOf2 p.n
  else if p.k < 1 then
    .moduleRankTooSmall p.k
  else if p.eta > 4 then
    .errorBoundTooLarge p.eta 4
  else if p.q < p.n then
    .modulusTooSmall p.q
  else
    .ok

/-- Check if MLWE parameters are valid (boolean) -/
def MLWEParams.isValid (p : MLWEParams) : Bool :=
  p.validate = .ok

/-- Check if MLWE parameters are secure (Prop) -/
def MLWEParams.isSecure (p : MLWEParams) : Prop :=
  p.n ≥ minSecureDimension ∧
  p.k ≥ 1 ∧
  p.eta ≤ 4

-- Security-bit estimates are not computed here; use external lattice-estimator.
def SISParams.estimatedSecurityBits (p : SISParams) : Option Nat := none
def MLWEParams.estimatedSecurityBits (p : MLWEParams) : Option Nat := none

/-- Validate that our concrete NIST-aligned parameter sets are valid -/
theorem sisL1_valid : sisL1.isValid = true := by native_decide
theorem sisL3_valid : sisL3.isValid = true := by native_decide
theorem sisL5_valid : sisL5.isValid = true := by native_decide
theorem mlweL1_valid : mlweL1.isValid = true := by native_decide
theorem mlweL3_valid : mlweL3.isValid = true := by native_decide
theorem mlweL5_valid : mlweL5.isValid = true := by native_decide

/-- Combined validation for a full lattice assumption set -/
def LatticeAssumptions.validate (A : LatticeAssumptions S) : Bool :=
  A.sisInst.isValid && A.mlweInst.isValid

/-- Human-readable security summary (bit estimates external). -/
structure SecuritySummary where
  sisValid : Bool
  mlweValid : Bool
  sisSecurityBits : Option Nat
  mlweSecurityBits : Option Nat
  overallSecurityBits : Option Nat  -- min if both available
  deriving Repr

/-- Generate security summary for lattice assumptions -/
def LatticeAssumptions.securitySummary (A : LatticeAssumptions S) : SecuritySummary :=
  let sisBits := A.sisInst.estimatedSecurityBits
  let mlweBits := A.mlweInst.estimatedSecurityBits
  { sisValid := A.sisInst.isValid
    mlweValid := A.mlweInst.isValid
    sisSecurityBits := sisBits
    mlweSecurityBits := mlweBits
    overallSecurityBits := Option.map2 min sisBits mlweBits }

end IceNine.Security
