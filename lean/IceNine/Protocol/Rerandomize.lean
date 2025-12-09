/-
# Rerandomized signing (zero-sum masks on shares/nonces)
-/

import IceNine.Protocol.Core
import IceNine.Protocol.Sign

namespace IceNine.Protocol

/--
  Apply zero-sum masks to signing shares and nonces; assumes masks over active
  participants sum to zero in both Secret and nonce space.
-/
structure RerandMasks (S : Scheme) :=
  (shareMask : S.PartyId → S.Secret)
  (nonceMask : S.PartyId → S.Secret)
  (shareSumZero : ∀ (Sset : List S.PartyId), (Sset.map shareMask).sum = 0)
  (nonceSumZero : ∀ (Sset : List S.PartyId), (Sset.map nonceMask).sum = 0)

/--
  Rerandomize a signing local state.
-/
def rerandState
  (S : Scheme)
  (masks : RerandMasks S)
  (st : SignLocalState S) : SignLocalState S :=
{ st with
  y_i := st.y_i + masks.nonceMask st.share.pid,
  w_i := S.A (st.y_i + masks.nonceMask st.share.pid),
  share := { st.share with sk_i := st.share.sk_i + masks.shareMask st.share.pid,
                           pk_i := S.A (st.share.sk_i + masks.shareMask st.share.pid) } }

/--
  Verification invariant: rerandomizing with zero-sum masks preserves the final signature.
-/
lemma rerand_preserves_sig
  (S : Scheme)
  (masks : RerandMasks S)
  (Sset : List S.PartyId)
  (c : S.Challenge)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S)) :
  -- If share masks sum to zero over Sset, aggregated z unchanged.
  (shares.map (fun sh => masks.shareMask sh.from)).sum = 0 →
  aggregateSignature S c Sset commits (shares.map (fun sh => { sh with z_i := sh.z_i + masks.shareMask sh.from }))
    = aggregateSignature S c Sset commits shares := by
  intro hzero
  -- reuse aggregateSignature_masks_zero
  have := aggregateSignature_masks_zero S c Sset commits shares (fun pid => masks.shareMask pid) hzero
  -- shares.map over pid matches the mask map we use
  simpa using this

end IceNine.Protocol
