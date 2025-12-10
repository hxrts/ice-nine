/-
# Extension Security Integration

Re-exports and integration lemmas for extension protocols:
- Refresh: zero-sum masks preserve public key
- Rerandomization: zero-sum masks preserve signature

These lemmas connect the extension protocols to the core security proofs,
showing that refresh/rerand operations maintain protocol invariants.
-/

import IceNine.Protocol.Refresh
import IceNine.Protocol.Repair
import IceNine.Protocol.Rerandomize
import IceNine.Security.Repair
import IceNine.Security.Sign

namespace IceNine.Security.RefreshRepair

open IceNine.Protocol
open List

/-!
## Refresh Invariants

Key property: zero-sum masks don't change the aggregate public key.
A(sk_i + mask_i) = A(sk_i) + A(mask_i), and Σ A(mask_i) = A(Σ mask_i) = A(0) = 0.
-/

/-- Refresh preserves global pk: Σ pk'_i = Σ pk_i when Σ mask_i = 0.
    Uses linearity of A and zero-sum property. -/
lemma refresh_pk_unchanged
  (S : Scheme)
  (m : MaskFn S)
  (shares : List (KeyShare S))
  (hsum : (shares.map (fun ks => m.mask ks.pid)).sum = 0) :
  let refreshed := refreshShares S m shares
  (refreshed.map (·.pk_i)).sum = (shares.map (·.pk_i)).sum := by
  classical
  unfold refreshShares
  simp only [List.map_map, Function.comp]
  -- Split: Σ pk'_i = Σ pk_i + Σ A(mask_i)
  have hsplit :
    (shares.map (fun ks => S.A (ks.sk_i + m.mask ks.pid))).sum
    = (shares.map (·.pk_i)).sum + (shares.map (fun ks => S.A (m.mask ks.pid))).sum := by
    simp only [List.map_map, Function.comp]
    induction shares with
    | nil => simp
    | cons ks rest ih =>
        simp only [List.map_cons, List.sum_cons, LinearMap.map_add]
        rw [ih]; ring
  -- Linearity: Σ A(mask_i) = A(Σ mask_i)
  have hA : (shares.map (fun ks => S.A (m.mask ks.pid))).sum
      = S.A ((shares.map (fun ks => m.mask ks.pid)).sum) := by
    induction shares with
    | nil => simp
    | cons ks rest ih =>
        simp only [List.map_cons, List.sum_cons, LinearMap.map_add]
        rw [ih]
  -- Zero-sum: A(0) = 0
  simp only [hsplit, hA, hsum, map_zero, add_zero]

/-!
## Rerandomization Invariants

Rerandomization masks preserve the final signature.
Zero-sum masks on z_i values cancel in aggregate.
-/

/-- Rerandomization preserves signature: masked shares aggregate to same sig.
    Delegates to Sign.aggregateSignature_masks_zero. -/
lemma rerand_preserves_sig
  (S : Scheme)
  (masks : RerandMasks S)
  (Sset : List S.PartyId)
  (c : S.Challenge)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S)) :
  (shares.map (fun sh => masks.shareMask sh.sender)).sum = 0 →
  aggregateSignature S c Sset commits (shares.map (fun sh => { sh with z_i := sh.z_i + masks.shareMask sh.sender }))
    = aggregateSignature S c Sset commits shares := by
  intro hzero
  apply IceNine.Security.Sign.aggregateSignature_masks_zero
  · exact hzero

end IceNine.Security.RefreshRepair
