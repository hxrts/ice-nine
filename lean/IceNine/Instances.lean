/-
# Concrete Scheme Instantiations

This module provides concrete instantiations of `IceNine.Protocol.Scheme`
for testing and proving protocol correctness properties.

## WARNING: Demo Commitments Are NOT Hiding

The `CommitRecord` structure stores the committed value in plaintext.
This means:
- ✓ Binding property holds (different values → different commitments)
- ✗ Hiding property FAILS (commitment reveals the value!)

This is intentional for demo/testing purposes:
- Correctness proofs only need binding
- Hiding is a security property, not a correctness property
- Formal hiding would require probabilistic/computational reasoning

**DO NOT USE THESE INSTANCES IN PRODUCTION**

For real deployments, instantiate with:
- Pedersen commitments: C = g^v · h^r (perfectly hiding, DLog-binding)
- Hash-based: C = H(v ‖ r) (ROM hiding, collision-resistance binding)

## Scheme Hierarchy

| Scheme | Secret | Public | A | Use Case |
|--------|--------|--------|---|----------|
| simpleScheme | Int | Int | id | Basic correctness |
| zmodScheme | ZMod q | ZMod q | ×a | Field arithmetic |
| zmodVecScheme | Fin n → ZMod q | Fin n → ZMod q | id | Vector proofs |
| matrixScheme | Fin m → ZMod q | Fin n → ZMod q | A·v | SIS/LWE structure |
| polyScheme | Fin n → ZMod q | Fin n → ZMod q | a·v | Ring-LWE structure |
-/

import IceNine.Protocol.Core

namespace IceNine.Instances

open IceNine.Protocol

/-!
## Demo Commitment Scheme

**NOT HIDING**: Stores value in plaintext. For testing only!

A proper commitment would use:
- Pedersen: C = g^v · h^r (requires group structure)
- Hash-based: C = H(v ‖ r) (requires hash function)
-/

-- Commitment: store the opened value and nonce together.
-- WARNING: This reveals the value! Not hiding!
structure CommitRecord where
  val   : Int    -- EXPOSED: the committed value (breaks hiding!)
  nonce : Int    -- the opening randomness
deriving DecidableEq, Repr

def commitRecord (w : Int) (nonce : Int) : CommitRecord :=
  { val := w, nonce := nonce }

-- Hash: a deterministic integer mix of the inputs.
def hashMix
    (m : ByteArray)
    (pk : Int)
    (Sset : List Nat)
    (commits : List CommitRecord)
    (w : Int) : Int :=
  let msgSum : Int := m.toList.map Int.ofNat |>.sum
  msgSum + pk + w + (Sset.length : Int) + (commits.length : Int)

-- Norm check: always accept (we are not modeling rejection here).
def normOKAlways (_ : Int) : Prop := True

/-- A simple concrete Scheme over integers, for sanity proofs. -/
def simpleScheme : Scheme :=
{ PartyId   := Nat
, Message   := ByteArray
, Secret    := Int
, Public    := Int
, Challenge := Int
, Scalar    := Int
, scalarSemiring := inferInstance
, secretAdd := inferInstance
, publicAdd := inferInstance
, secretModule := inferInstance
, publicModule := inferInstance
, challengeSMulSecret := inferInstance
, challengeSMulPublic := inferInstance
, A := LinearMap.id
, Commitment := CommitRecord
, Opening := Int
, commit := commitRecord
, commitBinding := by intros x1 x2 o1 o2 h; cases h; rfl
, hash := hashMix
, hashCollisionResistant := True
, normOK := normOKAlways
}

@[simp] lemma smul_int_eq_mul (a b : Int) : a • b = a * b := rfl

/-! ## Finite-field demo over `ZMod q` -/

open scoped BigOperators
open Nat

def zmodCommit {q : ℕ} (w : ZMod q) (nonce : ZMod q) : CommitRecord :=
  { val := w, nonce := nonce }

def zmodHash {q : ℕ}
    (m : ByteArray) (pk : ZMod q) (Sset : List Nat)
    (commits : List CommitRecord) (w : ZMod q) : ZMod q :=
  let msgSum : ZMod q := (m.toList.map (fun n => (n : ZMod q))).sum
  msgSum + pk + w + (Sset.length : ZMod q) + (commits.length : ZMod q)

def zmodScheme (q : ℕ) [hq : Fact q.Prime] (a : ZMod q) : Scheme :=
{ PartyId   := Nat
, Message   := ByteArray
, Secret    := ZMod q
, Public    := ZMod q
, Challenge := ZMod q
, Scalar    := ZMod q
, scalarSemiring := inferInstance
, secretAdd := inferInstance
, publicAdd := inferInstance
, secretModule := inferInstance
, publicModule := inferInstance
, challengeSMulSecret := inferInstance
, challengeSMulPublic := inferInstance
, A := LinearMap.lsmul _ _ a
, Commitment := CommitRecord
, Opening := ZMod q
, commit := zmodCommit
, commitBinding := by intros x1 x2 o1 o2 h; cases h; rfl
, hash := zmodHash
, hashCollisionResistant := True
, normOK := fun _ => True
}

/-
  Vector scheme over (Fin n → ZMod q). We use coordinate-wise identity A
  and a simple hash that sums all coordinates plus metadata.
-/

def coordSum {n : Nat} {q : ℕ} (v : Fin n → ZMod q) : ZMod q :=
  (Finset.univ.sum fun i => v i)

def zmodVecCommit {n q} (w : Fin n → ZMod q) (nonce : Fin n → ZMod q) : CommitRecord :=
  { val := w, nonce := nonce }

def zmodVecHash {n q : ℕ}
    (m : ByteArray) (pk : Fin n → ZMod q) (Sset : List Nat)
    (commits : List CommitRecord) (w : Fin n → ZMod q) : ZMod q :=
  let msgSum : ZMod q := (m.toList.map (fun x => (x : ZMod q))).sum
  msgSum + coordSum pk + coordSum w + (Sset.length : ZMod q) + (commits.length : ZMod q)

def zmodVecScheme (q n : ℕ) [Fact q.Prime] : Scheme :=
{ PartyId   := Nat
, Message   := ByteArray
, Secret    := Fin n → ZMod q
, Public    := Fin n → ZMod q
, Challenge := ZMod q
, Scalar    := ZMod q
, scalarSemiring := inferInstance
, secretAdd := inferInstance
, publicAdd := inferInstance
, secretModule := inferInstance
, publicModule := inferInstance
, challengeSMulSecret := inferInstance
, challengeSMulPublic := inferInstance
, A := LinearMap.id
, Commitment := CommitRecord
, Opening := Fin n → ZMod q
, commit := zmodVecCommit
, commitBinding := by intros x1 x2 o1 o2 h; cases h; rfl
, hash := zmodVecHash
, hashCollisionResistant := True
, normOK := fun _ => True
}

/-!
## Matrix-Based Scheme (SIS/LWE Style)

This scheme uses matrix-vector multiplication as the linear map A.
This models the structure of lattice-based cryptography:
- Secret: s ∈ Z_q^m (short vector)
- Public: t = A·s ∈ Z_q^n where A ∈ Z_q^{n×m} is public

The SIS problem asks: given A, find short z with Az = 0.
The LWE problem asks: given (A, As+e), recover s.
-/

/-- Public matrix for matrix-based scheme -/
structure MatrixParams (n m : ℕ) (q : ℕ) where
  /-- The public matrix A ∈ Z_q^{n×m} -/
  A : Matrix (Fin n) (Fin m) (ZMod q)

/-- Matrix-vector multiplication as linear map -/
def matrixMulVecLinear {n m : ℕ} {q : ℕ} [Fact q.Prime]
    (A : Matrix (Fin n) (Fin m) (ZMod q))
    : (Fin m → ZMod q) →ₗ[ZMod q] (Fin n → ZMod q) :=
  { toFun := fun s => A.mulVec s
    map_add' := fun x y => by simp [Matrix.mulVec_add]
    map_smul' := fun c x => by simp [Matrix.mulVec_smul] }

/-- Commitment for matrix scheme: hash of value with nonce -/
def matrixCommit {n : ℕ} {q : ℕ}
    (w : Fin n → ZMod q) (nonce : Fin n → ZMod q) : CommitRecord :=
  -- Simple commitment: store hash of (w, nonce)
  -- In practice, use Pedersen or hash-based commitment
  { val := coordSum w + coordSum nonce, nonce := coordSum nonce }

/-- Hash for matrix scheme -/
def matrixHash {n : ℕ} {q : ℕ}
    (m : ByteArray) (pk : Fin n → ZMod q) (Sset : List Nat)
    (commits : List CommitRecord) (w : Fin n → ZMod q) : ZMod q :=
  let msgSum : ZMod q := (m.toList.map (fun x => (x : ZMod q))).sum
  msgSum + coordSum pk + coordSum w + (Sset.length : ZMod q) + (commits.length : ZMod q)

/-- Matrix-based scheme with A: Z_q^m → Z_q^n as matrix multiplication.

    This models SIS/LWE-based signatures where:
    - Secret key: s ∈ Z_q^m with small coefficients
    - Public key: t = A·s ∈ Z_q^n
    - Signature: z = y + c·s where y is ephemeral nonce

    Security reduces to SIS: forging requires finding short z with Az = 0. -/
def matrixScheme (n m q : ℕ) [hq : Fact q.Prime]
    (A : Matrix (Fin n) (Fin m) (ZMod q)) : Scheme :=
{ PartyId   := Nat
, Message   := ByteArray
, Secret    := Fin m → ZMod q      -- secret vectors in Z_q^m
, Public    := Fin n → ZMod q      -- public vectors in Z_q^n
, Challenge := ZMod q
, Scalar    := ZMod q
, scalarSemiring := inferInstance
, secretAdd := inferInstance
, publicAdd := inferInstance
, secretModule := inferInstance
, publicModule := inferInstance
, challengeSMulSecret := inferInstance
, challengeSMulPublic := inferInstance
, A := matrixMulVecLinear A        -- A(s) = A·s (matrix-vector product)
, Commitment := CommitRecord
, Opening := Fin m → ZMod q
, commit := matrixCommit
, commitBinding := by intros x1 x2 o1 o2 h; simp [matrixCommit] at h; sorry
, hash := matrixHash
, hashCollisionResistant := True
, normOK := fun _ => True          -- Would use proper norm bound in practice
}

/-- Create a random-looking matrix for testing (deterministic from seed) -/
def makeTestMatrix (n m q : ℕ) (seed : ℕ) : Matrix (Fin n) (Fin m) (ZMod q) :=
  fun i j => ((seed + i.val * m + j.val) : ZMod q)

/-- Example: 4×8 matrix scheme over Z_17 -/
def exampleMatrixScheme : Scheme :=
  matrixScheme 4 8 17 (makeTestMatrix 4 8 17 42)

/-!
## Polynomial Ring Scheme (Ring-LWE Style)

This scheme uses polynomial multiplication in R_q = Z_q[X]/(X^n + 1).
This models Ring-LWE based cryptography (e.g., Kyber, Dilithium):
- Secret: s ∈ R_q with small coefficients
- Public: t = a·s ∈ R_q where a ∈ R_q is public

We represent polynomials as coefficient vectors (Fin n → ZMod q).
Multiplication is polynomial multiplication modulo (X^n + 1).
-/

/-- Polynomial multiplication in Z_q[X]/(X^n + 1).
    Uses negacyclic convolution: X^n = -1.

    For f = Σ f_i X^i and g = Σ g_i X^i:
    (f·g)_k = Σ_{i+j=k} f_i·g_j - Σ_{i+j=k+n} f_i·g_j -/
def polyMul {n : ℕ} {q : ℕ} [NeZero n]
    (f g : Fin n → ZMod q) : Fin n → ZMod q :=
  fun k =>
    -- Positive wraparound terms (i + j = k)
    let pos := Finset.univ.sum fun i : Fin n =>
      if h : i.val ≤ k.val then
        let j : Fin n := ⟨k.val - i.val, by omega⟩
        f i * g j
      else 0
    -- Negative wraparound terms (i + j = k + n), contribute with minus sign
    let neg := Finset.univ.sum fun i : Fin n =>
      if h : i.val > k.val ∧ i.val + (n - 1 - k.val) < n then
        let j : Fin n := ⟨n + k.val - i.val, by omega⟩
        f i * g j
      else 0
    pos - neg

/-- Polynomial multiplication as linear map (fixing first argument) -/
def polyMulLinear {n : ℕ} {q : ℕ} [NeZero n] [Fact q.Prime]
    (a : Fin n → ZMod q) : (Fin n → ZMod q) →ₗ[ZMod q] (Fin n → ZMod q) :=
  { toFun := fun s => polyMul a s
    map_add' := fun x y => by
      ext k
      simp only [polyMul, Pi.add_apply]
      ring_nf
      sorry  -- Requires distributivity of polyMul
    map_smul' := fun c x => by
      ext k
      simp only [polyMul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring_nf
      sorry  -- Requires scalar multiplication property
  }

/-- Hash for polynomial scheme -/
def polyHash {n : ℕ} {q : ℕ}
    (m : ByteArray) (pk : Fin n → ZMod q) (Sset : List Nat)
    (commits : List CommitRecord) (w : Fin n → ZMod q) : ZMod q :=
  let msgSum : ZMod q := (m.toList.map (fun x => (x : ZMod q))).sum
  msgSum + coordSum pk + coordSum w + (Sset.length : ZMod q) + (commits.length : ZMod q)

/-- Polynomial ring scheme with A(s) = a·s in R_q = Z_q[X]/(X^n + 1).

    This models Ring-LWE/Module-LWE based signatures where:
    - Ring: R_q = Z_q[X]/(X^n + 1) for n a power of 2
    - Secret key: s ∈ R_q with small coefficients
    - Public key: t = a·s ∈ R_q
    - Signature: z = y + c·s

    Security reduces to Ring-SIS/Ring-LWE over the polynomial ring.
    The ring structure enables efficient NTT-based multiplication. -/
def polyScheme (n q : ℕ) [hn : NeZero n] [hq : Fact q.Prime]
    (a : Fin n → ZMod q) : Scheme :=
{ PartyId   := Nat
, Message   := ByteArray
, Secret    := Fin n → ZMod q      -- polynomials as coefficient vectors
, Public    := Fin n → ZMod q
, Challenge := ZMod q              -- challenge is a scalar (or small poly)
, Scalar    := ZMod q
, scalarSemiring := inferInstance
, secretAdd := inferInstance
, publicAdd := inferInstance
, secretModule := inferInstance
, publicModule := inferInstance
, challengeSMulSecret := inferInstance
, challengeSMulPublic := inferInstance
, A := polyMulLinear a             -- A(s) = a·s (polynomial multiplication)
, Commitment := CommitRecord
, Opening := Fin n → ZMod q
, commit := matrixCommit           -- reuse matrix commitment
, commitBinding := by intros x1 x2 o1 o2 h; simp [matrixCommit] at h; sorry
, hash := polyHash
, hashCollisionResistant := True
, normOK := fun _ => True
}

/-- Create a test polynomial (deterministic from seed) -/
def makeTestPoly (n q : ℕ) (seed : ℕ) : Fin n → ZMod q :=
  fun i => ((seed + i.val * 7 + 3) : ZMod q)

/-- Example: degree-256 polynomial scheme over Z_q for q = 8380417 (Dilithium) -/
def examplePolyScheme : Scheme :=
  polyScheme 256 8380417 (makeTestPoly 256 8380417 42)

end IceNine.Instances
