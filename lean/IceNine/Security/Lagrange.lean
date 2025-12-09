/-
# Lagrange-weighted correctness lemmas
-/

import Mathlib
import IceNine.Protocol.Sign
import IceNine.Instances

namespace IceNine.Security

open IceNine.Protocol
open IceNine.Instances

lemma sum_zipWith_scaled_add_mul (c : Int) :
  ∀ (ys sks coeffs : List Int),
    (List.zipWith3 (fun λ y s => λ * y + λ * (c * s)) coeffs ys sks).sum
      = (coeffs.zipWith (·*·) ys).sum + c * (coeffs.zipWith (·*·) sks).sum
  | [], [], [] => by simp
  | [], _, _ => by simp
  | _, [], _ => by simp
  | _, _, [] => by simp
  | λ::λs, y::ys, s::sks =>
      have ih := sum_zipWith_scaled_add_mul ys sks λs
      simp [List.sum_cons, ih, mul_add, add_assoc, add_left_comm, add_comm, left_distrib, right_distrib, mul_comm, mul_left_comm]

lemma verify_happy_simple_lagrange
    (ys sks coeffs : List Int)
    (m : ByteArray)
    (Sset : List Nat)
    (session fromId : Nat) :
  let pk : Int := (coeffs.zipWith (·*·) sks).sum
  let w  : Int := (coeffs.zipWith (·*·) ys).sum
  let c  : Int := simpleScheme.hash m pk Sset [] w
  let coeffStructs : List (LagrangeCoeff simpleScheme) :=
    coeffs.map (fun λ => { pid := fromId, lambda := λ })
  let shares : List (SignShareMsg simpleScheme) :=
    List.zipWith (fun y s => { from := fromId, session := session, z_i := y + c * s }) ys sks
  let sig : Signature simpleScheme :=
    aggregateSignatureLagrange simpleScheme c Sset [] coeffStructs shares
  verify simpleScheme pk m sig := by
  intros pk w c coeffStructs shares sig
  simp [aggregateSignatureLagrange, verify, simpleScheme, normOKAlways,
        smul_int_eq_mul, sum_zipWith_scaled_add_mul, LinearMap.id_apply, List.zipWith, List.zipWith3, List.foldl_map] at *
  ring_nf

end IceNine.Security
