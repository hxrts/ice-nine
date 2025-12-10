/-
# Composite CRDT State

Combines all protocol state into a single CRDT-mergeable structure:
- Phase state (commit/reveal/shares/done)
- Refresh state (share rerandomization masks)
- Repair state (share recovery messages)
- Rerandomization state (signature privacy masks)

Product semilattice instances handle merge automatically.
-/

import IceNine.Protocol.Phase
import IceNine.Protocol.RefreshState
import IceNine.Protocol.Repair
import IceNine.Protocol.Rerandomize
import IceNine.Protocol.StateProduct

namespace IceNine.Protocol

/-!
## Composite State

Single type for all protocol state. Each component is a CRDT:
- State S p: phase-indexed signing state
- RefreshState S: accumulated refresh masks
- RepairBundle S: repair messages for share recovery
- RerandMasks S: rerandomization masks for privacy

Merge is componentwise via product semilattice.
-/

/-- Complete protocol state as a 4-tuple.
    Merge via product semilattice: (a₁⊔b₁, a₂⊔b₂, a₃⊔b₃, a₄⊔b₄). -/
abbrev CompositeState (S : Scheme) [DecidableEq S.PartyId] (p : Phase) :=
  (State S p) × RefreshState S × RepairBundle S × RerandMasks S

-- Merge is provided by product semilattice instances from StateProduct.
-- No additional code needed: `(a, b, c, d) ⊔ (a', b', c', d')` just works.

end IceNine.Protocol
