/-
# Refresh, Repair, Rerandomize invariants

This module re-exports key lemmas from the security modules for convenience
and provides integration lemmas for the extensions.
-/

import IceNine.Protocol.Refresh
import IceNine.Protocol.Repair
import IceNine.Protocol.Rerandomize
import IceNine.Security.Repair
import IceNine.Security.Sign

namespace IceNine.Security.RefreshRepair

open IceNine.Protocol
open List

/-! ## Refresh Invariants -/

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

/-! ## Rerandomization Invariants -/

lemma rerand_preserves_sig
  (S : Scheme)
  (masks : RerandMasks S)
  (Sset : List S.PartyId)
  (c : S.Challenge)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S)) :
  (shares.map (fun sh => masks.shareMask sh.from)).sum = 0 →
  aggregateSignature S c Sset commits (shares.map (fun sh => { sh with z_i := sh.z_i + masks.shareMask sh.from }))
    = aggregateSignature S c Sset commits shares := by
  intro hzero
  apply IceNine.Security.Sign.aggregateSignature_masks_zero
  · exact hzero

end IceNine.Security.RefreshRepair
