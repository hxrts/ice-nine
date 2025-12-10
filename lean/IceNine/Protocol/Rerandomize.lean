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
ephemeral nonce y_i. Both must sum to zero over the signer set.
-/

/-- Zero-sum masks for rerandomizing signatures.
    Σ_i shareMask(i) = 0 and Σ_i nonceMask(i) = 0 over signer set. -/
structure RerandMasks (S : Scheme) :=
  (shareMask    : S.PartyId → S.Secret)  -- mask for long-term shares
  (nonceMask    : S.PartyId → S.Secret)  -- mask for ephemeral nonces
  -- Zero-sum invariants (for any signer set)
  (shareSumZero : ∀ (Sset : List S.PartyId), (Sset.map shareMask).sum = 0)
  (nonceSumZero : ∀ (Sset : List S.PartyId), (Sset.map nonceMask).sum = 0)

/-- CRDT merge: pointwise addition of masks.
    Preserves zero-sum: (a+b).sum = a.sum + b.sum = 0 + 0 = 0. -/
instance (S : Scheme) : Join (RerandMasks S) :=
  ⟨fun a b =>
    { shareMask := fun pid => a.shareMask pid + b.shareMask pid
    , nonceMask := fun pid => a.nonceMask pid + b.nonceMask pid
    , shareSumZero := by intro Sset; simp only [List.map_map, List.sum_map_add]; simp [a.shareSumZero Sset, b.shareSumZero Sset]
    , nonceSumZero := by intro Sset; simp only [List.map_map, List.sum_map_add]; simp [a.nonceSumZero Sset, b.nonceSumZero Sset] }⟩

/-!
## State Rerandomization

Apply masks to signing state. The aggregated signature is unchanged
because mask contributions cancel: Σ (z_i + mask_i) = Σ z_i.
-/

/-- Apply rerandomization masks to signing local state.
    Updates both long-term share and ephemeral nonce. -/
def rerandState
  (S : Scheme)
  (masks : RerandMasks S)
  (st : SignLocalState S) : SignLocalState S :=
{ st with
  -- Rerandomize ephemeral nonce
  y_i := st.y_i + masks.nonceMask st.share.pid,
  -- Recompute public nonce
  w_i := S.A (st.y_i + masks.nonceMask st.share.pid),
  -- Rerandomize long-term share
  share := { st.share with sk_i := st.share.sk_i + masks.shareMask st.share.pid,
                           pk_i := S.A (st.share.sk_i + masks.shareMask st.share.pid) } }

end IceNine.Protocol
