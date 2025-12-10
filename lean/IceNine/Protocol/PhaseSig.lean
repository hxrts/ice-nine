/-
# Phase-restricted signature extraction

Signatures can only be extracted from the `done` phase; earlier phases cannot
produce them by construction. We extend this to carry a threshold context so
callers must provide the active set and card proof alongside the final sig.
-/

import IceNine.Protocol.Phase
import IceNine.Protocol.Sign

namespace IceNine.Protocol

def extractSignature (S : Scheme) : State S .done → Signature S
  | ⟨sig⟩ => sig

structure DoneWithCtx (S : Scheme) :=
  (ctx : ThresholdCtx S)
  (sig : Signature S)

def extractSignatureWithCtx (S : Scheme) : DoneWithCtx S → Signature S
  | ⟨_, sig⟩ => sig

-- There is no extractor from earlier phases; this is enforced by the type.

end IceNine.Protocol
