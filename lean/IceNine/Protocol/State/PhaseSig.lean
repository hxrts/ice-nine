/-
# Phase-Restricted Signature Extraction

Type-level enforcement: signatures can ONLY be extracted from .done phase.
There is no function to extract from commit/reveal/shares phases.
This prevents returning incomplete signatures by construction.
-/

import IceNine.Protocol.State.Phase
import IceNine.Protocol.Sign.Types
import IceNine.Protocol.Sign.Threshold

namespace IceNine.Protocol

/-!
## Basic Extraction

Simple extraction from done state. Type system ensures this is the only
path to get a Signature from protocol state.
-/

/-- Extract signature from done state.
    Uses DoneState (alias for SignatureDone) from Types.lean. -/
def extractSignature (S : Scheme) : DoneState S → Signature S
  | ⟨sig⟩ => sig

/-!
## Extraction with Context

For callers that need threshold context alongside the signature.
Pairs the ThresholdCtx (active set + threshold proof) with final sig.
-/

/-- Done state paired with threshold context for verification.

    NOTE: Repr is not derived because ThresholdCtx contains proofs
    and Signature contains arbitrary scheme types. -/
structure DoneWithCtx (S : Scheme) [DecidableEq S.PartyId] where
  ctx : ThresholdCtx S  -- active set + threshold proof
  sig : Signature S     -- final signature

/-- Extract signature, discarding context (already verified). -/
def extractSignatureWithCtx (S : Scheme) [DecidableEq S.PartyId] : DoneWithCtx S → Signature S
  | ⟨_, sig⟩ => sig

-- NOTE: No extractors exist for earlier phases. This is by design.
-- The DoneState type is the only one that contains a completed Signature.

end IceNine.Protocol
