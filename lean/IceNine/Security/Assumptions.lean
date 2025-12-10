/-
# Security Assumptions

Abstract security assumptions for threshold signature proofs:
- Random Oracle model for hash function
- Binding property for commitments
- Norm bounds for lattice security (SIS/LWE hardness)
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

/-- Concrete SIS parameters for ~128-bit security (Dilithium-style) -/
def sis128 : SISParams :=
  { n := 256, m := 512, q := 8380417, beta := 78
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

/-- Concrete MLWE parameters for ~128-bit security (Dilithium-style) -/
def mlwe128 : MLWEParams :=
  { n := 256, k := 4, q := 8380417, eta := 2 }

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
## Assumption Bundle

Packages all cryptographic assumptions needed for security proofs.
Concrete instantiations must prove these properties hold.
-/

/-- Security assumptions for threshold signature scheme. -/
structure Assumptions (S : Scheme) where
  /-- Hash function modeled as random oracle -/
  hashRO          : Prop
  /-- Commitment scheme is binding (can't open to different values) -/
  commitBinding   : Prop := S.hashCollisionResistant
  /-- Norm bounds prevent leakage in lattice setting -/
  normLeakageBound : Prop
  /-- Max corrupted parties (must be < threshold for security) -/
  corruptionBound : Nat
  /-- SIS parameters for unforgeability -/
  sisParams : Option SISParams := none
  /-- MLWE parameters for key secrecy -/
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
  A.hashRO ∧ A.commitBinding ∧ A.normLeakageBound

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

### SIS Security Requirements

For SIS(n, m, q, β) to be hard:
1. **Dimension**: n ≥ 256 for post-quantum security
2. **Columns**: m ≥ 2n (enough room for short solutions)
3. **Solution bound**: β < q/2 (meaningful shortness constraint)
4. **Modulus**: q prime or prime power (for algebraic structure)

### MLWE Security Requirements

For MLWE(n, k, q, η) to be hard:
1. **Ring dimension**: n ≥ 256, power of 2 for NTT
2. **Module rank**: k ≥ 2 (k=1 is Ring-LWE)
3. **Error bound**: η small (typically ≤ 4)
4. **Modulus**: q ≡ 1 (mod 2n) for NTT-friendly
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

/-- Estimated SIS security bits (very rough heuristic).
    Real analysis needs BKZ cost estimation. -/
def SISParams.estimatedSecurityBits (p : SISParams) : Nat :=
  if p.isValid then
    -- Rough heuristic: security grows with n, decreases with β
    -- This is NOT rigorous!
    min p.n (p.n * p.q / (p.beta + 1) / 1000)
  else 0

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

/-- Estimated MLWE security bits (very rough heuristic).
    Real analysis needs LWE estimator. -/
def MLWEParams.estimatedSecurityBits (p : MLWEParams) : Nat :=
  if p.isValid then
    -- Rough heuristic: security ≈ n * k / 2
    -- This is NOT rigorous!
    p.n * p.k / 2
  else 0

/-- Validate that our concrete parameter sets are valid -/
theorem sis128_valid : sis128.isValid = true := by native_decide
theorem mlwe128_valid : mlwe128.isValid = true := by native_decide

/-- Combined validation for a full lattice assumption set -/
def LatticeAssumptions.validate (A : LatticeAssumptions S) : Bool :=
  A.sisInst.isValid && A.mlweInst.isValid

/-- Human-readable security summary -/
structure SecuritySummary where
  sisValid : Bool
  mlweValid : Bool
  sisSecurityBits : Nat
  mlweSecurityBits : Nat
  overallSecurityBits : Nat  -- min of both
  deriving Repr

/-- Generate security summary for lattice assumptions -/
def LatticeAssumptions.securitySummary (A : LatticeAssumptions S) : SecuritySummary :=
  let sisBits := A.sisInst.estimatedSecurityBits
  let mlweBits := A.mlweInst.estimatedSecurityBits
  { sisValid := A.sisInst.isValid
    mlweValid := A.mlweInst.isValid
    sisSecurityBits := sisBits
    mlweSecurityBits := mlweBits
    overallSecurityBits := min sisBits mlweBits }

end IceNine.Security
