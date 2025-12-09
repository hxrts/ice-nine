/-
# Share refresh/removal via zero-sum masks

This version uses an explicit mask function together with a proof that the
masked contributions sum to zero over the current participant set, making the
pk-invariance lemma straightforward.
-/

import IceNine.Protocol.Core

namespace IceNine.Protocol

open List

/-- Mask function for shares. -/
structure MaskFn (S : Scheme) :=
  (mask : S.PartyId → S.Secret)

/--
  Refresh shares by adding masks; pk stays unchanged if mask sums to zero over
  the active participant list.
-/
def refreshShares
  (S : Scheme)
  (m : MaskFn S)
  (shares : List (KeyShare S)) : List (KeyShare S) :=
  shares.map (fun ks =>
    let sk' := ks.sk_i + m.mask ks.pid
    let pk' := S.A sk'
    { ks with sk_i := sk', pk_i := pk' })

/-- If mask sums to zero over the participant set, refreshed pk equals original pk. -/
lemma refresh_pk_unchanged
  (S : Scheme)
  (m : MaskFn S)
  (shares : List (KeyShare S))
  (hsum : (shares.map (fun ks => m.mask ks.pid)).sum = 0) :
  let refreshed := refreshShares S m shares
  (refreshed.foldl (fun acc ks => acc + ks.pk_i) (0 : S.Public)) =
  (shares.foldl (fun acc ks => acc + ks.pk_i) (0 : S.Public)) := by
  classical
  unfold refreshShares
  -- separate base pk sum and mask contribution
  have hsplit :
    (shares.map (fun ks =>
        let sk' := ks.sk_i + m.mask ks.pid
        let pk' := S.A sk'
        { ks with sk_i := sk', pk_i := pk' })).foldl (fun acc ks => acc + ks.pk_i) 0
    =
    shares.foldl (fun acc ks => acc + ks.pk_i) 0
      + shares.foldl (fun acc ks => acc + S.A (m.mask ks.pid)) 0 := by
    revert shares
    induction shares with
    | nil => simp
    | cons ks rest ih =>
        simp [ih, add_assoc, add_left_comm, add_comm, LinearMap.map_add]
  have hA :
    shares.foldl (fun acc ks => acc + S.A (m.mask ks.pid)) 0
      = S.A ((shares.map (fun ks => m.mask ks.pid)).sum) := by
    revert shares; intro sh; induction sh with
    | nil => simp
    | cons ks rest ih =>
        simp [ih, add_comm, add_left_comm, add_assoc, LinearMap.map_add]
  have hmask : shares.foldl (fun acc ks => acc + S.A (m.mask ks.pid)) 0 = 0 := by
    simp [hA, hsum]
  have := hsplit
  simp [hmask, add_comm] at this
  simpa using this

end IceNine.Protocol
