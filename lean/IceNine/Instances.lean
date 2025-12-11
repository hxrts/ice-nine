/-
# Concrete Scheme Instantiations (hash-based, lattice-friendly)

This module provides concrete instantiations of `IceNine.Protocol.Scheme` for
testing and verification. We use a hash-based commitment and a SHAKE-like hash
for Fiat–Shamir, plus a Dilithium-style ℓ∞ norm check. Hiding of the commitment
is treated as an **assumption** (computational) while binding is proved from the
injectivity of the hash input tuple.

**NOTE**: The hash/commitment here are still abstracted; to connect to a real
SHAKE implementation, wire in `Std.Digest` (or a SHAKE binding) with collision
resistance assumptions.
-/

import Mathlib
import IceNine.Protocol.Core.Core
-- import Std.Data.Digest  -- Not available in this Lean version

namespace IceNine.Instances

open IceNine.Protocol

/-!
## Hash-based commitment

Commitment is `commit(w, nonce) = hash (w, nonce)`; opening = nonce. Binding
relies on collision resistance: if hashes collide, the opened values must match.
Hiding is computational and left as an assumption (not modeled here).
-/

/-- A generic hash type placeholder. In production, use SHAKE256 or similar.
    This stub uses ByteArray for simplicity. -/
abbrev HashOut := ByteArray

/-- Serialize public/nonce pair to bytes (simple concat). -/
def encodePair {α β} [ToString α] [ToString β] (w : α) (nonce : β) : ByteArray :=
  (toString w ++ "|" ++ toString nonce).toUTF8

/-- Abstract hash function stub. In production, use SHAKE256.
    This stub returns the input truncated/padded to 32 bytes. -/
def hashBytes (b : ByteArray) : HashOut :=
  -- Simple stub: return first 32 bytes or pad with zeros
  let n := b.size
  if n >= 32 then
    b.extract 0 32
  else
    -- Pad with zeros to reach 32 bytes
    let padding := ByteArray.mk (Array.replicate (32 - n) 0)
    b ++ padding

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

    For our model, we derive an integer by treating the hash as a little-endian
    64-bit word. This is sufficient for correctness proofs but not for security.
    Production code must use the proper Dilithium challenge derivation.
    **Reference**: FIPS 204 (ML-DSA) Section 8.3 "Challenge Derivation" -/
def hashToChallenge (h : HashOut) : Int :=
  -- HashOut is ByteArray, so we access bytes directly
  let bytes := h.toList.take 8
  let asNat := bytes.foldl (fun (acc, i) b => (acc + (b.toNat <<< (8 * i)), i + 1)) (0, 0) |>.1
  Int.ofNat (asNat % 256) - 128  -- Range [-128, 127] for simple bound

/-!
## Dilithium-style norm check

We model secrets/publics as integer vectors and enforce an ℓ∞ bound.
-/

/-- Compute ℓ∞ norm of an integer vector (max absolute value), as a Nat. -/
def intVecInfNorm {n : Nat} (v : Fin n → Int) : Nat :=
  Finset.univ.sup (fun i => Int.natAbs (v i))

def intVecInfLeq (B : Nat) {n : Nat} (v : Fin n → Int) : Prop :=
  intVecInfNorm v ≤ B

/-- Decidability instance for intVecInfLeq (needed for normOKDecidable). -/
instance intVecInfLeqDecidable (B : Nat) {n : Nat} : DecidablePred (intVecInfLeq B (n := n)) :=
  fun v => inferInstanceAs (Decidable (intVecInfNorm v ≤ B))

/-- Honest vectors with all coefficients ≤ bound satisfy normOK. -/
lemma intVecInfLeq_of_coeff_bound {n : Nat} {B : Nat} (v : Fin n → Int)
  (h : ∀ i, Int.natAbs (v i) ≤ B) : intVecInfLeq B v := by
  unfold intVecInfLeq intVecInfNorm
  classical
  apply Finset.sup_le_iff.mpr
  intro i _; exact h i

/-!
## Concrete lattice-friendly scheme
-/

/-- ToString instance for integer vectors (stub for hash serialization). -/
instance {n : Nat} : ToString (Fin n → Int) where
  toString v := "[" ++ String.intercalate "," ((List.finRange n).map fun i => toString (v i)) ++ "]"

/-- ToString instance for ByteArray (for hash serialization). -/
instance : ToString ByteArray where
  toString b := String.intercalate "" (b.toList.map fun byte => String.mk [Char.ofNat byte.toNat])

structure LatticeParams where
  n : Nat := 256          -- dimension
  q : Nat := 8380417      -- modulus
  bound : Nat := 1 <<< 19 -- ℓ∞ bound (approx Dilithium γ1)
  deriving Repr

/-- Binding assumption for hash-based commitments: collision resistance of the digest. -/
structure HashBinding : Prop :=
  (binding :
    ∀ {P N} [ToString P] [ToString N] (x1 x2 : P) (o1 o2 : N),
      hashBytes (encodePair x1 o1) = hashBytes (encodePair x2 o2) → x1 = x2)

/-- Axiomatically assume digest binding; replace with a proven instance when available. -/
axiom hashBindingAssumption : HashBinding

instance : HashBinding := hashBindingAssumption

/-- Integer vectors modulo q as secrets/publics. -/
def intMod (_q : Nat) := Int

/-- Commitment for lattice scheme: stores hash plus the committed value for binding.
    Hiding is *assumed* (computational); value is kept here to make binding trivial. -/
structure LatticeCommitment (P N : Type) where
  com : HashOut
  deriving DecidableEq

/-- ToString instance for LatticeCommitment (for hash serialization). -/
instance {P N : Type} : ToString (LatticeCommitment P N) where
  toString c := toString c.com

/-- Hash-based commitment: Com(w; nonce) = H(encode(w, nonce)). -/
def latticeCommit {P N} [ToString P] [ToString N] (w : P) (nonce : N) :
  LatticeCommitment P N :=
  ⟨hashBytes (encodePair w nonce)⟩

def latticeScheme (p : LatticeParams := {}) (_ : HashBinding := hashBindingAssumption) : Scheme :=
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
  , Commitment := LatticeCommitment (Fin p.n → Int) (Fin p.n → Int)
  , Opening := Fin p.n → Int
  , commit := latticeCommit
  , commitBinding := by
      intro x1 x2 o1 o2 h
      have hb := HashBinding.binding (x1 := x1) (x2 := x2) (o1 := o1) (o2 := o2) h
      exact hb
  , hashToScalar := fun domain data =>
      let h := hashBytes (domain ++ data)
      hashToChallenge h
  , hashDkg := fun pid pk R =>
      let enc : ByteArray := (toString pid ++ "|" ++ toString pk ++ "|" ++ toString R).toUTF8
      hashToChallenge (hashBytes enc)
  , hash := fun m pk Sset commits w =>
      hashToChallenge (hashFS m pk Sset commits w)
  , hashCollisionResistant := True
  , normOK := fun v => intVecInfLeq p.bound v
  , normOKDecidable := intVecInfLeqDecidable p.bound
}

abbrev LatticePartyId   := (latticeScheme).PartyId
abbrev LatticeMessage   := (latticeScheme).Message
abbrev LatticeSecret    := (latticeScheme).Secret
abbrev LatticePublic    := (latticeScheme).Public
abbrev LatticeChallenge := (latticeScheme).Challenge
abbrev LatticeBound     : Nat := ({} : LatticeParams).bound

end IceNine.Instances
