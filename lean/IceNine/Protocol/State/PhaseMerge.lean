/-
# Composite CRDT State

Combines all protocol state into a single CRDT-mergeable structure:
- Phase state (commit/reveal/shares/done)
- Refresh state (share rerandomization masks)
- Repair state (share recovery messages)
- Rerandomization state (signature privacy masks)

Product semilattice instances handle merge automatically.
-/

import IceNine.Protocol.State.Phase
import IceNine.Protocol.Shares.RefreshState
import IceNine.Protocol.Shares.Repair
import IceNine.Protocol.Shares.Rerandomize
import Mathlib

namespace IceNine.Protocol

/-!
## Composite State

Single type for all protocol state. Each component is a CRDT:
- Phase.State S p: phase-indexed signing state
- RefreshState S: accumulated refresh masks
- RepairBundle S: repair messages for share recovery
- RawRerandMasks S: rerandomization masks for privacy

Merge is componentwise via product semilattice.
-/

/-
NOTE: CompositeState type is commented out because there's no unified Phase.State type.
The phase-specific states (CommitState, RevealState, ShareState) are separate structures.
For a unified state, use PhaseIndexed.PhaseState from State/PhaseIndexed.lean instead.

/-- Complete protocol state as a 4-tuple.
    Merge via product semilattice: (a₁⊔b₁, a₂⊔b₂, a₃⊔b₃, a₄⊔b₄).

    NOTE: Uses RawRerandMasks instead of RerandMasks because the signer set
    is not known at the type level. Zero-sum property is verified separately. -/
abbrev CompositeState (S : Scheme) [DecidableEq S.PartyId] (p : Phase) :=
  (Phase.State S p) × RefreshState S × RepairBundle S × RawRerandMasks S
-/

-- Merge is provided by Mathlib's product semilattice instances.
-- `(a, b, c, d) ⊔ (a', b', c', d')` works out of the box.

end IceNine.Protocol
