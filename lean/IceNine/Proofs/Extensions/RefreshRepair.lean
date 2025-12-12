/-
# Extension Security Integration

Re-exports and integration lemmas for extension protocols:
- Refresh: zero-sum masks preserve public key
- Rerandomization: zero-sum masks preserve signature

These lemmas connect the extension protocols to the core security proofs,
showing that refresh/rerand operations maintain protocol invariants.
-/

import IceNine.Protocol.Shares.Refresh
import IceNine.Protocol.Shares.Repair
import IceNine.Protocol.Shares.Rerandomize
import IceNine.Proofs.Extensions.Repair
import IceNine.Proofs.Correctness.Sign

namespace IceNine.Proofs.Extensions.RefreshRepair

open IceNine.Protocol
open List

/-!
## Refresh Invariants

Key property: zero-sum masks don't change the aggregate public key.
A(sk_i + mask_i) = A(sk_i) + A(mask_i), and Σ A(mask_i) = A(Σ mask_i) = A(0) = 0.
-/

/-- Refresh preserves global pk: Σ pk'_i = Σ pk_i when Σ mask_i = 0.
    Uses linearity of A and zero-sum property.

    **Mathematical justification**:
    - For each share: pk'_i = A(sk_i + mask_i) = A(sk_i) + A(mask_i) = pk_i + A(mask_i)
    - Summing: Σ pk'_i = Σ pk_i + Σ A(mask_i)
    - By linearity: Σ A(mask_i) = A(Σ mask_i) = A(0) = 0
    - Therefore: Σ pk'_i = Σ pk_i

    NOTE: Uses sorry due to complex type class constraints for induction over lists
    with the Scheme's linear map properties. -/
lemma refresh_pk_unchanged
  (S : Scheme)
  (m : MaskFn S)
  (shares : List (KeyShare S))
  (hsum : (shares.map (fun ks => m.mask ks.pid)).sum = 0) :
  let refreshed := refreshShares S m shares
  (refreshed.map (·.pk_i)).sum = (shares.map (·.pk_i)).sum := by
  sorry

/-!
## Rerandomization Invariants

Rerandomization masks preserve the final signature.
Zero-sum masks on z_i values cancel in aggregate.
-/

/-- Rerandomization preserves signature using raw masks.
    Requires explicit proof that masks sum to zero. -/
lemma rerand_preserves_sig_raw
  (S : Scheme)
  (masks : RawRerandMasks S)
  (Sset : List S.PartyId)
  (c : S.Challenge)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S)) :
  (shares.map (fun sh => masks.shareMask sh.sender)).sum = 0 →
  aggregateSignature S c Sset commits (shares.map (fun sh => { sh with z_i := sh.z_i + masks.shareMask sh.sender }))
    = aggregateSignature S c Sset commits shares := by
  intro hzero
  apply IceNine.Proofs.Correctness.Sign.aggregateSignature_masks_zero
  · exact hzero

/-- Rerandomization preserves signature using zero-sum masks.
    Zero-sum property is carried in the RerandMasks structure.

    NOTE: Uses sorry due to complex type-dependent rewrite issues when
    connecting the party ID list in RerandMasks to the actual shares list. -/
lemma rerand_preserves_sig
  (S : Scheme)
  (Sset : List S.PartyId)
  (masks : RerandMasks S Sset)
  (c : S.Challenge)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  (hpids : shares.map (·.sender) = Sset) :
  aggregateSignature S c Sset commits (shares.map (fun sh => { sh with z_i := sh.z_i + masks.shareMask sh.sender }))
    = aggregateSignature S c Sset commits shares := by
  sorry

end IceNine.Proofs.Extensions.RefreshRepair
