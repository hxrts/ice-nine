/-
# Rerandomized Signing

Apply zero-sum masks to both long-term shares and ephemeral nonces.
Because masks sum to zero over the signer set, the aggregated signature
is unchanged while individual contributions are hidden.

Use case: Prevents observers from correlating signatures across sessions
by making each party's contribution look random.
-/

import IceNine.Protocol.Core
import IceNine.Protocol.Sign

namespace IceNine.Protocol

/-!
## Rerandomization Masks

Two masks are applied: one to the long-term share sk_i, one to the
ephemeral nonce y_i. Both must sum to zero over the specific signer set.

**Design Note**: The structure is parameterized by the signer set `Sset` to
avoid an overly strong claim that masks sum to zero for ANY list. The zero-sum
property only holds for the specific set the masks were generated for.
-/

/-- Raw mask functions without zero-sum proof.
    Use `RerandMasks` when you need the zero-sum guarantee. -/
structure RawRerandMasks (S : Scheme) :=
  (shareMask : S.PartyId → S.Secret)  -- mask for long-term shares
  (nonceMask : S.PartyId → S.Secret)  -- mask for ephemeral nonces

/-- CRDT merge for raw masks: pointwise addition. -/
instance (S : Scheme) : Join (RawRerandMasks S) :=
  ⟨fun a b =>
    { shareMask := fun pid => a.shareMask pid + b.shareMask pid
    , nonceMask := fun pid => a.nonceMask pid + b.nonceMask pid }⟩

/-- Zero-sum masks for rerandomizing signatures over a specific signer set.
    Σ_{i∈Sset} shareMask(i) = 0 and Σ_{i∈Sset} nonceMask(i) = 0. -/
structure RerandMasks (S : Scheme) (Sset : List S.PartyId) :=
  (masks : RawRerandMasks S)
  -- Zero-sum invariants for the specific signer set
  (shareSumZero : (Sset.map masks.shareMask).sum = 0)
  (nonceSumZero : (Sset.map masks.nonceMask).sum = 0)

/-- CRDT merge for zero-sum masks: pointwise addition preserves zero-sum.
    (a+b).sum = a.sum + b.sum = 0 + 0 = 0. -/
instance (S : Scheme) (Sset : List S.PartyId) : Join (RerandMasks S Sset) :=
  ⟨fun a b =>
    { masks := a.masks ⊔ b.masks
    , shareSumZero := by
        simp only [Join.join, List.map_map, List.sum_map_add]
        simp [a.shareSumZero, b.shareSumZero]
    , nonceSumZero := by
        simp only [Join.join, List.map_map, List.sum_map_add]
        simp [a.nonceSumZero, b.nonceSumZero] }⟩

/-- Convenience accessor for share mask -/
def RerandMasks.shareMask (m : RerandMasks S Sset) : S.PartyId → S.Secret :=
  m.masks.shareMask

/-- Convenience accessor for nonce mask -/
def RerandMasks.nonceMask (m : RerandMasks S Sset) : S.PartyId → S.Secret :=
  m.masks.nonceMask

/-!
## State Rerandomization

Apply masks to signing state. The aggregated signature is unchanged
because mask contributions cancel: Σ (z_i + mask_i) = Σ z_i.
-/

/-- Apply raw rerandomization masks to signing local state.
    Updates both long-term share and ephemeral nonce.
    Use this when you have raw masks and will prove zero-sum separately. -/
def rerandStateRaw
  (S : Scheme)
  (masks : RawRerandMasks S)
  (st : SignLocalState S) : SignLocalState S :=
{ st with
  -- Rerandomize ephemeral nonce
  y_i := st.y_i + masks.nonceMask st.share.pid,
  -- Recompute public nonce
  w_i := S.A (st.y_i + masks.nonceMask st.share.pid),
  -- Rerandomize long-term share
  share := { st.share with sk_i := st.share.sk_i + masks.shareMask st.share.pid,
                           pk_i := S.A (st.share.sk_i + masks.shareMask st.share.pid) } }

/-- Apply zero-sum rerandomization masks to signing local state.
    The zero-sum property guarantees the aggregated signature is preserved. -/
def rerandState
  (S : Scheme)
  (Sset : List S.PartyId)
  (masks : RerandMasks S Sset)
  (st : SignLocalState S) : SignLocalState S :=
  rerandStateRaw S masks.masks st

end IceNine.Protocol
