/-
# CRDT integration for refresh masks

We lift MaskFn into a semilattice state so it can be merged alongside protocol
state. Zero-sum is required at use sites for pk invariance.
-/

import IceNine.Protocol.Phase
import IceNine.Protocol.Refresh

namespace IceNine.Protocol

structure RefreshState (S : Scheme) :=
  (mask : MaskFn S)

instance (S : Scheme) : Join (RefreshState S) :=
  ⟨fun a b => { mask := { mask := fun pid => a.mask.mask pid + b.mask.mask pid } }⟩

instance (S : Scheme) : SemilatticeSup (RefreshState S) := by infer_instance

end IceNine.Protocol
