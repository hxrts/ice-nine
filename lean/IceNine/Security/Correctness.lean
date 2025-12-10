/-
# Signature Correctness Proofs

Happy-path correctness: when all parties behave honestly, verification
succeeds. Core algebraic insight: linearity of A and signature equation.

z = Σ z_i = Σ (y_i + c·sk_i) = Σy_i + c·Σsk_i = y + c·sk
A(z) = A(y) + c·A(sk) = w + c·pk
So: A(z) - c·pk = w ✓
-/

import Mathlib
import IceNine.Protocol.Core
import IceNine.Protocol.DKGCore
import IceNine.Protocol.Sign
import IceNine.Instances
import IceNine.Norms

namespace IceNine.Security

open IceNine.Protocol
open IceNine.Instances
open IceNine.Norms

/-!
## Core Algebraic Lemmas

The key insight: z_i = y_i + c·sk_i sums linearly.
Σ(y_i + c·sk_i) = Σy_i + c·Σsk_i
-/

/-- Linearity of partial signature aggregation for integers.
    Σ(y_i + c·sk_i) splits into Σy_i + c·Σsk_i. -/
lemma sum_zipWith_add_mul (c : Int) :
  ∀ (ys sks : List Int),
    (List.zipWith (fun y s => y + c * s) ys sks).sum
      = ys.sum + c * sks.sum
  | [], [] => by simp
  | [], _  => by simp
  | _ , [] => by simp
  | y::ys, s::sks =>
      have ih := sum_zipWith_add_mul ys sks
      simp [ih, List.sum_cons, add_assoc, add_left_comm, add_comm, mul_add, add_mul]

/-!
## Integer Scheme Correctness

Verify honest execution on the simple bounded integer scheme.
-/

/-- Happy-path correctness: honest signers produce valid signature.
    Uses simpleSchemeBounded with norm bound B. -/
theorem verify_happy_simple
    (ys sks : List Int)         -- ephemeral nonces and secret shares
    (m : ByteArray)             -- message
    (Sset : List Nat)           -- signer set
    (session fromId : Nat)
    (B : Int := 1000) :
  let scheme := simpleSchemeBounded B
  let pk : Int := sks.sum       -- global secret key = Σ sk_i
  let w  : Int := ys.sum        -- aggregate nonce = Σ y_i
  let c  : Int := scheme.hash m pk Sset [] w
  let shares : List (SignShareMsg scheme) :=
    List.zipWith (fun y s => { sender := fromId, session := session, z_i := y + c * s }) ys sks
  let sig : Signature scheme := aggregateSignature scheme c Sset [] shares
  verify scheme pk m sig := by
  intros pk w c shares sig
  simp [aggregateSignature, verify, simpleSchemeBounded, intLeqBound,
        sum_zipWith_add_mul, smul_int_eq_mul, LinearMap.id_apply] at *
  ring

/-- Sanity check: concrete example with ys=[1], sks=[2]. -/
example :
  verify (simpleSchemeBounded 10)
    ([2].sum)
    ByteArray.empty
    (aggregateSignature (simpleSchemeBounded 10)
        ((simpleSchemeBounded 10).hash ByteArray.empty ([2].sum) [0] [] ([1].sum))
        [0] []
        (List.zipWith (fun y s => { sender := 0, session := 0, z_i := y + ((simpleSchemeBounded 10).hash ByteArray.empty ([2].sum) [0] [] ([1].sum)) * s })
          [1] [2])) := by
  simpa using
    (verify_happy_simple (ys := [1]) (sks := [2]) (m := ByteArray.empty) (Sset := [0]) (session := 0) (fromId := 0) (B := 10))

/-!
## Module-General Correctness

Generalize to any R-module (needed for ZMod vectors, lattices, etc.).
-/

/-- Module-general linearity: works for any semiring R and module M.
    Σ(y_i + c•sk_i) = Σy_i + c•Σsk_i. -/
lemma sum_zipWith_add_smul
    {R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]
    (c : R) :
  ∀ (ys sks : List M),
    (List.zipWith (fun y s => y + c • s) ys sks).sum
      = ys.sum + c • sks.sum
  | [], [] => by simp
  | [], _  => by simp
  | _ , [] => by simp
  | y::ys, s::sks =>
      have ih := sum_zipWith_add_smul ys sks
      simp [ih, List.sum_cons, add_assoc, add_left_comm, add_comm, smul_add, add_smul]

/-!
## ZMod Vector Scheme Correctness

Finite-field vector scheme used as a simple algebraic surrogate for the lattice
instantiation. The proof shape matches the lattice case (linearity over a
module), but works over `ZMod q` to keep the example short.
-/

/-- Happy-path correctness for ZMod vector scheme.
    Shares are vectors in (ZMod q)^n. -/
theorem verify_happy_zmod_vec
    {q n : Nat} [Fact q.Prime]
    (ys sks : List (Fin n → ZMod q))  -- vectors in (Z/qZ)^n
    (m : ByteArray)
    (Sset : List Nat)
    (session fromId : Nat) :
  let S := zmodVecScheme q n
  let pk := sks.sum
  let w  := ys.sum
  let c  : ZMod q := S.hash m pk Sset [] w
  let shares : List (SignShareMsg S) :=
    List.zipWith (fun y s => { sender := fromId, session := session, z_i := y + c • s }) ys sks
  let sig : Signature S := aggregateSignature S c Sset [] shares
  verify S pk m sig := by
  intros S pk w c shares sig
  classical
  simp [aggregateSignature, verify, zmodVecScheme, zmodVecHash, zmodVecCommit,
        sum_zipWith_add_smul, coordSum, LinearMap.id_apply,
        smul_add, add_comm, add_left_comm, add_assoc] at *
  abel

end IceNine.Security
