/-
# Norm predicates for demo instances

We implement simple ℓ∞ bounds for integers and ZMod, and adjust the demo
schemes to use them.
-/

import IceNine.Instances
import Mathlib

namespace IceNine.Norms

open IceNine.Instances

-- ℓ∞ bound for integers
def intLeqBound (B : Int) (x : Int) : Prop := Int.abs x ≤ B

-- For vectors, one would lift this to lists; we keep scalar for demo.

-- ℓ∞ bound for ZMod by lifting to representatives
def zmodLeqBound {q : ℕ} (B : Nat) (x : ZMod q) : Prop :=
  (Int.natAbs x.val) ≤ B

-- Replace normOK in the simpleScheme with a parameterized bound.
def simpleSchemeBounded (B : Int) : IceNine.Protocol.Core.Scheme :=
  { simpleScheme with normOK := intLeqBound B }

def zmodSchemeBounded (q : ℕ) [Fact q.Prime] (a : ZMod q) (B : Nat) :
    IceNine.Protocol.Core.Scheme :=
  { zmodScheme q a with normOK := zmodLeqBound B }

end IceNine.Norms
