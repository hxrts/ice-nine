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

-- Merge is provided by Mathlib's product semilattice instances.
-- `(a, b, c, d) ⊔ (a', b', c', d')` works out of the box.

end IceNine.Protocol
