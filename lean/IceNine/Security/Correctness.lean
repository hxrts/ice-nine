/-
# Correctness lemmas (happy path)
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

/-- Helper: sum of zipWith (y + c*s) splits into separate sums (integers). -/
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

/--
  Happy-path correctness for the bounded integer scheme.
-/
theorem verify_happy_simple
    (ys sks : List Int)
    (m : ByteArray)
    (Sset : List Nat)
    (session fromId : Nat)
    (B : Int := 1000) :
  let scheme := simpleSchemeBounded B
  let pk : Int := sks.sum
  let w  : Int := ys.sum
  let c  : Int := scheme.hash m pk Sset [] w
  let shares : List (SignShareMsg scheme) :=
    List.zipWith (fun y s => { from := fromId, session := session, z_i := y + c * s }) ys sks
  let sig : Signature scheme := aggregateSignature scheme c Sset [] shares
  verify scheme pk m sig := by
  intros pk w c shares sig
  simp [aggregateSignature, verify, simpleSchemeBounded, intLeqBound,
        sum_zipWith_add_mul, smul_int_eq_mul, LinearMap.id_apply] at *
  ring

/-- Sample integer sanity check. -/
example :
  verify (simpleSchemeBounded 10)
    ([2].sum)
    ByteArray.empty
    (aggregateSignature (simpleSchemeBounded 10)
        ((simpleSchemeBounded 10).hash ByteArray.empty ([2].sum) [0] [] ([1].sum))
        [0] []
        (List.zipWith (fun y s => { from := 0, session := 0, z_i := y + ((simpleSchemeBounded 10).hash ByteArray.empty ([2].sum) [0] [] ([1].sum)) * s })
          [1] [2])) := by
  simpa using
    (verify_happy_simple (ys := [1]) (sks := [2]) (m := ByteArray.empty) (Sset := [0]) (session := 0) (fromId := 0) (B := 10))

/-- Module-general version of the zipWith linearity lemma. -/
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

/--
  Honest-path correctness for the vector ZMod scheme.
-/
theorem verify_happy_zmod_vec
    {q n : Nat} [Fact q.Prime]
    (ys sks : List (Fin n → ZMod q))
    (m : ByteArray)
    (Sset : List Nat)
    (session fromId : Nat) :
  let S := zmodVecScheme q n
  let pk := sks.sum
  let w  := ys.sum
  let c  : ZMod q := S.hash m pk Sset [] w
  let shares : List (SignShareMsg S) :=
    List.zipWith (fun y s => { from := fromId, session := session, z_i := y + c • s }) ys sks
  let sig : Signature S := aggregateSignature S c Sset [] shares
  verify S pk m sig := by
  intros S pk w c shares sig
  classical
  simp [aggregateSignature, verify, zmodVecScheme, zmodVecHash, zmodVecCommit,
        sum_zipWith_add_smul, coordSum, LinearMap.id_apply,
        smul_add, add_comm, add_left_comm, add_assoc] at *
  abel

end IceNine.Security
