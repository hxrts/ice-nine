/-
# Unified merge for protocol state and auxiliary CRDT data

We pair a phase state with refresh, repair, and rerandomization state, and
provide a single merge operator (semilattice join) for the composite.
-/

import IceNine.Protocol.Phase
import IceNine.Protocol.RefreshState
import IceNine.Protocol.Repair
import IceNine.Protocol.Rerandomize
import IceNine.Protocol.StateProduct

namespace IceNine.Protocol

-- Composite state: phase state × refresh mask × repair bundle × rerand masks.
abbrev CompositeState (S : Scheme) (p : Phase) :=
  (State S p) × RefreshState S × RepairBundle S × RerandMasks S

-- Merge is provided by product semilattice instances; no extra code needed.

end IceNine.Protocol
