/-
# Refresh State for CRDT Integration

Wraps MaskFn in a semilattice-compatible state structure so refresh
masks can be merged alongside other protocol state (signing, repair, etc.).
The zero-sum property is verified at use sites, not enforced structurally.
-/

import IceNine.Protocol.State.Phase
import IceNine.Protocol.Shares.Refresh

namespace IceNine.Protocol

/-!
## Refresh State

RefreshState wraps a MaskFn to participate in the CRDT composite state.
Multiple refresh contributions merge via pointwise mask addition.
-/

/-- Refresh state for CRDT merging. Wraps MaskFn.
    Zero-sum property checked when refresh is applied. -/
structure RefreshState (S : Scheme) where
  mask : MaskFn S

/-- CRDT merge: combine refresh contributions pointwise. -/
instance (S : Scheme) : Join (RefreshState S) :=
  ⟨fun a b => { mask := { mask := fun pid => a.mask.mask pid + b.mask.mask pid } }⟩

end IceNine.Protocol
