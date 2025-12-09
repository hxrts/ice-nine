/-
# Concrete scheme instantiation

This module provides a concrete instantiation of `IceNine.Protocol.Scheme`
so we can state and discharge correctness lemmas without committing to real
cryptography yet. It uses integers as both secrets and publics,
identity `A`, and a placeholder commitment/hash.
-/

import IceNine.Protocol.Core

namespace IceNine.Instances

open IceNine.Protocol

-- Commitment: store the opened value and nonce together.
structure CommitRecord where
  val   : Int
  nonce : Int
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

end IceNine.Instances
