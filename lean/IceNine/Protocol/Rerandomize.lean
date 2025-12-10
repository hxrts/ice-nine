/-
# Rerandomized signing (zero-sum masks on shares/nonces)
-/

import IceNine.Protocol.Core
import IceNine.Protocol.Sign

namespace IceNine.Protocol

/--
  Apply zero-sum masks to signing shares and nonces. Assumes masks over active
  participants sum to zero in both Secret and nonce space.
-/
structure RerandMasks (S : Scheme) :=
  (shareMask : S.PartyId → S.Secret)
  (nonceMask : S.PartyId → S.Secret)
  (shareSumZero : ∀ (Sset : List S.PartyId), (Sset.map shareMask).sum = 0)
  (nonceSumZero : ∀ (Sset : List S.PartyId), (Sset.map nonceMask).sum = 0)

-- Merge masks by pointwise addition. Zero-sum is preserved by additivity.
instance (S : Scheme) : Join (RerandMasks S) :=
  ⟨fun a b =>
    { shareMask := fun pid => a.shareMask pid + b.shareMask pid
    , nonceMask := fun pid => a.nonceMask pid + b.nonceMask pid
    , shareSumZero := by intro Sset; simp [a.shareSumZero Sset, b.shareSumZero Sset, add_comm, add_left_comm, add_assoc]
    , nonceSumZero := by intro Sset; simp [a.nonceSumZero Sset, b.nonceSumZero Sset, add_comm, add_left_comm, add_assoc] }⟩

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

end IceNine.Protocol
