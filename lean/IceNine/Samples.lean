/-
# Sample transcript generation

Convenient `#eval` snippets to emit small honest transcripts for manual inspection.
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.DKG.Core
import IceNine.Protocol.Sign.Sign
import IceNine.Instances
import IceNine.Norms

open IceNine.Protocol
open IceNine.Instances
open IceNine.Norms

def sampleTranscriptInt : IO Unit := do
  let scheme := simpleSchemeBounded 20
  let ys := [1, 2]
  let sks := [3, 4]
  let pk : Int := sks.sum
  let w  : Int := ys.sum
  let c  : Int := scheme.hash ByteArray.empty pk [0,1] [] w
  let shares : List (SignShareMsg scheme) :=
    List.zipWith (fun y s => { sender := 0, session := 0, z_i := y + c * s }) ys sks
  let sig : Signature scheme := aggregateSignature scheme c [0,1] [] shares
  IO.println s!"pk={pk}, w={w}, c={c}, z={sig.z}"

#eval sampleTranscriptInt

def sampleTranscriptZMod : IO Unit := do
  let S := zmodSchemeBounded 7 3 5  -- q=7, A=3, bound=5
  let ys : List (ZMod 7) := [1, 2]
  let sks : List (ZMod 7) := [3, 4]
  let pk : ZMod 7 := sks.sum
  let w  : ZMod 7 := ys.sum
  let c  : ZMod 7 := S.hash ByteArray.empty pk [0,1] [] w
  let shares : List (SignShareMsg S) :=
    List.zipWith (fun y s => { sender := 0, session := 0, z_i := y + c * s }) ys sks
  let sig : Signature S := aggregateSignature S c [0,1] [] shares
  IO.println s!"pk={pk}, w={w}, c={c}, z={sig.z}"

#eval sampleTranscriptZMod
