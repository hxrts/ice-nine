/-
# CRDT Merge Soundness

Re-exports for CRDT merge proofs from Proofs/Extensions/Phase.

The actual proofs live in `IceNine.Proofs.Extensions.Phase`. This module
provides aliases in the Soundness namespace for organizational clarity.

## Key Theorems

1. `MsgMap.senders_merge`: Merge preserves union of sender sets
2. `MsgMap.merge_senders_comm`: Sender sets are commutative under merge
3. `MsgMap.merge_idem`: Merge is idempotent

These properties ensure convergence in distributed state replication.
-/

import IceNine.Proofs.Extensions.Phase

set_option autoImplicit false

namespace IceNine.Proofs.Soundness.CRDT

open IceNine.Protocol
open IceNine.Proofs.Extensions.Phase

/-!
## Re-exports from Proofs/Extensions/Phase

The CRDT merge proofs are in `Proofs/Extensions/Phase.lean`.
This module provides aliases in the Soundness namespace.

**Key theorems (from Extensions.Phase):**
- `MsgMap.senders_merge`: (a ⊔ b).senders.toFinset = a.senders.toFinset ∪ b.senders.toFinset
- `MsgMap.merge_senders_comm`: (a ⊔ b).senders.toFinset = (b ⊔ a).senders.toFinset
- `MsgMap.merge_idem`: a ⊔ a = a
-/

/-- CRDT safety: merge preserves sender set semantics.
    Alias for `MsgMap.senders_merge` from Extensions.Phase. -/
theorem msgmap_merge_preserves_senders {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    [LawfulBEq S.PartyId] [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    (a b : MsgMap S M) :
    (a ⊔ b).senders.toFinset = a.senders.toFinset ∪ b.senders.toFinset :=
  MsgMap.senders_merge S a b

/-- CRDT commutativity: merge order doesn't affect sender sets.
    Alias for `MsgMap.merge_senders_comm` from Extensions.Phase. -/
theorem msgmap_merge_comm_senders {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    [LawfulBEq S.PartyId] [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    (a b : MsgMap S M) :
    (a ⊔ b).senders.toFinset = (b ⊔ a).senders.toFinset :=
  MsgMap.merge_senders_comm a b

/-- CRDT idempotence: merging with self is identity.
    Alias for `MsgMap.merge_idem` from Extensions.Phase. -/
theorem msgmap_merge_idem {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    (a : MsgMap S M) : a ⊔ a = a :=
  MsgMap.merge_idem a

end IceNine.Proofs.Soundness.CRDT
