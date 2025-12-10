/-
# Phase-Restricted Signature Extraction

Type-level enforcement: signatures can ONLY be extracted from .done phase.
There is no function to extract from commit/reveal/shares phases.
This prevents returning incomplete signatures by construction.
-/

import IceNine.Protocol.Phase
import IceNine.Protocol.Sign

namespace IceNine.Protocol

/-!
## Basic Extraction

Simple extraction from done state. Type system ensures this is the only
path to get a Signature from protocol state.
-/

/-- Extract signature from done phase.
    Type: State S .done → Signature S (no other phases possible). -/
def extractSignature (S : Scheme) [DecidableEq S.PartyId] : State S .done → Signature S
  | ⟨sig⟩ => sig

/-!
## Extraction with Context

For callers that need threshold context alongside the signature.
Pairs the ThresholdCtx (active set + threshold proof) with final sig.
-/

/-- Done state paired with threshold context for verification. -/
structure DoneWithCtx (S : Scheme) [DecidableEq S.PartyId] :=
  (ctx : ThresholdCtx S)  -- active set + threshold proof
  (sig : Signature S)     -- final signature
deriving Repr

/-- Extract signature, discarding context (already verified). -/
def extractSignatureWithCtx (S : Scheme) [DecidableEq S.PartyId] : DoneWithCtx S → Signature S
  | ⟨_, sig⟩ => sig

-- NOTE: No extractors exist for earlier phases. This is by design.
-- The type `State S .done` is the only one with a Signature inside.

end IceNine.Protocol
