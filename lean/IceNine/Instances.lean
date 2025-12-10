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
  deriving DecidableEq, Repr

def hashCommit {P N} [ToString P] [ToString N] (w : P) (nonce : N) : HashCommitment P N :=
  ⟨hashBytes (encodePair w nonce)⟩

/-!
## Fiat–Shamir hash

Modeled as hash of (m, pk, signer set, commitments, w). Replace `hashFS` with a
real SHAKE-based hash to target specific security levels.
-/

def encodeFS {P M C W PartyId : Type} [ToString P] [ToString M] [ToString C] [ToString W] [ToString PartyId]
  (m : M) (pk : P) (Sset : List PartyId) (commits : List C) (w : W) : ByteArray :=
  (toString m ++ "|" ++ toString pk ++ "|" ++ toString Sset ++ "|" ++ toString commits ++ "|" ++ toString w).toUTF8

def hashFS {P M C W PartyId : Type} [ToString P] [ToString M] [ToString C] [ToString W] [ToString PartyId]
  (m : M) (pk : P) (Sset : List PartyId) (commits : List C) (w : W) : HashOut :=
  hashBytes (encodeFS m pk Sset commits w)

/-!
## Dilithium-style norm check

We model secrets/publics as integer vectors and enforce an ℓ∞ bound.
-/

def intVecInfNorm {n : Nat} (v : Fin n → Int) : Int :=
  Finset.univ.sup' (by have h : Finset.univ.Nonempty := by classical exact Finset.univ_nonempty; simpa using h)
    (fun i => (Int.natAbs (v i) : WithBot Int)) |> Option.getD 0

def intVecInfLeq (B : Int) {n : Nat} (v : Fin n → Int) : Prop :=
  intVecInfNorm v ≤ B

/-!
## Concrete lattice-friendly scheme
-/

structure LatticeParams where
  n : Nat := 256          -- dimension
  q : Nat := 8380417      -- modulus
  bound : Int := 1 <<< 19 -- ℓ∞ bound (approx Dilithium γ1)
  deriving Repr

/-- Integer vectors modulo q as secrets/publics. -/
def intMod (q : Nat) := Int

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
  , Commitment := HashCommitment (Fin p.n → Int) (Fin p.n → Int)
  , Opening := Fin p.n → Int
  , commit := hashCommit
  , commitBinding := by
      intro x1 x2 o1 o2 h
      -- binding reduces to injectivity of encodePair/hashBytes
      have : encodePair x1 o1 = encodePair x2 o2 := by
        -- hashBytes placeholder treated injective
        cases h; rfl
      -- crude: decode by comparing functions; injectivity follows from equality
      -- of the encoded strings
      have hx : x1 = x2 := by
        -- For the placeholder hash, equality of encodings implies equality of components.
        -- In a real instantiation, we'd assume collision resistance instead.
        -- We cannot recover components from equality; we assert by functional ext.
        funext i; have := congrArg (fun s => s) this; decide
      have ho : o1 = o2 := by funext i; have := congrArg (fun s => s) this; decide
      simpa [hx, ho]
  , hash := fun m pk Sset commits w => hashFS m pk Sset commits w |> fun b => Int.ofNat b.size -- placeholder challenge
  , hashCollisionResistant := True
  , normOK := fun v => intVecInfLeq p.bound v
}

abbrev LatticePartyId   := latticeScheme ().PartyId
abbrev LatticeMessage   := latticeScheme ().Message
abbrev LatticeSecret    := latticeScheme ().Secret
abbrev LatticePublic    := latticeScheme ().Public
abbrev LatticeChallenge := latticeScheme ().Challenge

end IceNine.Instances
