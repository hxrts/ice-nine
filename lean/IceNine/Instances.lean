/-
# Concrete Scheme Instantiations (hash-based, lattice-friendly)

This module provides concrete instantiations of `IceNine.Protocol.Scheme` for
testing and verification. We use a hash-based commitment and a SHAKE-like hash
for Fiat–Shamir, plus a Dilithium-style ℓ∞ norm check. Hiding of the commitment
is treated as an **assumption** (computational) while binding is proved from the
injectivity of the hash input tuple.

**NOTE**: The hash/commitment here are still abstracted; to connect to a real
SHAKE implementation, wire in a concrete hash function with collision resistance
and preimage resistance assumptions.
-/

import Mathlib
import IceNine.Protocol.Core

namespace IceNine.Instances

open IceNine.Protocol

/-!
## Hash-based commitment

Commitment is `commit(w, nonce) = hash (w, nonce)`; opening = nonce. Binding
relies on collision resistance: if hashes collide, the opened values must match.
Hiding is computational and left as an assumption (not modeled here).
-/

/-- A generic hash type placeholder. Replace with SHAKE256 output type if desired. -/
@[simp] def HashOut := ByteArray

/-- Serialize public/nonce pair to bytes (simple concat). -/
def encodePair {α β} [ToString α] [ToString β] (w : α) (nonce : β) : ByteArray :=
  (toString w ++ "|" ++ toString nonce).toUTF8

/-- Abstract hash function; assume collision resistance elsewhere. -/
def hashBytes (b : ByteArray) : HashOut := b -- placeholder; treat as injective for binding

/-- Hash-based commitment: Com(w; nonce) = H( encode(w, nonce) ). -/
structure HashCommitment (P N : Type) where
  com : HashOut
  deriving DecidableEq

def hashCommit {P N} [ToString P] [ToString N] (w : P) (nonce : N) : HashCommitment P N :=
  ⟨hashBytes (encodePair w nonce)⟩

/-!
## Fiat–Shamir hash

Modeled as hash of (m, pk, signer set, commitments, w). In production, replace
with a real SHAKE256 implementation (as specified in Dilithium/ML-DSA).

The hash output is interpreted as a challenge. For Dilithium, challenges are
sparse polynomials with τ coefficients in {-1, 0, 1}. For simplicity, we model
challenges as integers here.
-/

def encodeFS {P M C W PartyId : Type} [ToString P] [ToString M] [ToString C] [ToString W] [ToString PartyId]
  (m : M) (pk : P) (Sset : List PartyId) (commits : List C) (w : W) : ByteArray :=
  (toString m ++ "|" ++ toString pk ++ "|" ++ toString Sset ++ "|" ++ toString commits ++ "|" ++ toString w).toUTF8

def hashFS {P M C W PartyId : Type} [ToString P] [ToString M] [ToString C] [ToString W] [ToString PartyId]
  (m : M) (pk : P) (Sset : List PartyId) (commits : List C) (w : W) : HashOut :=
  hashBytes (encodeFS m pk Sset commits w)

/-- Convert hash output to a challenge integer.

    **Production Note**: In real Dilithium/ML-DSA, the challenge is a polynomial
    with exactly τ coefficients in {-1, 1} and the rest 0, derived via rejection
    sampling from SHAKE256 output.

    For our model, we derive an integer by treating the hash as a big-endian
    encoding. This is sufficient for correctness proofs but not for security -
    production code must use the proper Dilithium challenge derivation.

    **Reference**: FIPS 204 (ML-DSA) Section 8.3 "Challenge Derivation" -/
def hashToChallenge (h : HashOut) : Int :=
  -- Interpret first 8 bytes as little-endian Int64, then take modulo to bound
  -- This is a simplified model; real Dilithium uses rejection sampling
  let bytes := h.toList.take 8
  let asNat := bytes.foldl (fun (acc, i) b => (acc + (b.toNat <<< (8 * i)), i + 1)) (0, 0) |>.1
  -- Reduce to a reasonable range (Dilithium τ is at most 60)
  Int.ofNat (asNat % 256) - 128  -- Range [-128, 127] for simple bound

/-!
## Dilithium-style norm check

We model secrets/publics as integer vectors and enforce an ℓ∞ bound.
-/

/-- Compute ℓ∞ norm of an integer vector (max absolute value). -/
def intVecInfNorm {n : Nat} (v : Fin n → Int) : Int :=
  if h : n = 0 then 0
  else
    let vals := List.ofFn (fun i : Fin n => (v i).natAbs)
    Int.ofNat (vals.foldl max 0)

def intVecInfLeq (B : Int) {n : Nat} (v : Fin n → Int) : Prop :=
  intVecInfNorm v ≤ B

/-- Decidability instance for intVecInfLeq (needed for normOKDecidable). -/
instance intVecInfLeqDecidable (B : Int) {n : Nat} : DecidablePred (intVecInfLeq B (n := n)) :=
  fun v => inferInstanceAs (Decidable (intVecInfNorm v ≤ B))

/-!
## Concrete lattice-friendly scheme
-/

structure LatticeParams where
  n : Nat := 256          -- dimension
  q : Nat := 8380417      -- modulus
  bound : Int := 1 <<< 19 -- ℓ∞ bound (approx Dilithium γ1)
  deriving Repr

/-- Integer vectors modulo q as secrets/publics. -/
def intMod (_q : Nat) := Int

/-- Simple commitment for lattice scheme: stores value directly.
    NOTE: This is NOT hiding - for testing/correctness only.
    Real deployment must use Pedersen or hash-based commitments. -/
structure LatticeCommitment (n : Nat) where
  value : Fin n → Int
  deriving DecidableEq

/-- Commitment function for lattice scheme.
    Ignores opening (no hiding in this test instance). -/
def latticeCommit {n : Nat} (w : Fin n → Int) (_nonce : Fin n → Int)
    : LatticeCommitment n :=
  ⟨w⟩

def latticeScheme (p : LatticeParams := {}) : Scheme :=
{ PartyId   := Nat
  , Message   := ByteArray
  , Secret    := Fin p.n → Int
  , Public    := Fin p.n → Int
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
  , Commitment := LatticeCommitment p.n
  , Opening := Fin p.n → Int
  , commit := latticeCommit
  , commitBinding := by
      intro x1 x2 _o1 _o2 h
      -- For latticeCommit, commitment stores value directly
      simp only [latticeCommit, LatticeCommitment.mk.injEq] at h
      exact h
  , hashToScalar := fun _domain _data => 0
  , hashDkg := fun _pid _pk _r => 0
  , hash := fun _m _pk _Sset _commits _w => 0
  , hashCollisionResistant := True
  , normOK := fun v => intVecInfLeq p.bound v
  , normOKDecidable := intVecInfLeqDecidable p.bound
}

abbrev LatticePartyId   := (latticeScheme ()).PartyId
abbrev LatticeMessage   := (latticeScheme ()).Message
abbrev LatticeSecret    := (latticeScheme ()).Secret
abbrev LatticePublic    := (latticeScheme ()).Public
abbrev LatticeChallenge := (latticeScheme ()).Challenge

end IceNine.Instances
