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

set_option autoImplicit false

namespace IceNine.Proofs.Extensions.RefreshRepair

open IceNine.Protocol
open List

/-!
## Refresh Invariants

Key property: zero-sum masks don't change the aggregate public key.
A(sk_i + mask_i) = A(sk_i) + A(mask_i), and Σ A(mask_i) = A(Σ mask_i) = A(0) = 0.
-/

/-- Helper: map over refreshShares extracts the pk_i values. -/
lemma refreshShares_pk_i_map
    (S : Scheme)
    (m : MaskFn S)
    (shares : List (KeyShare S)) :
    (refreshShares S m shares).map (·.pk_i) =
    shares.map (fun ks => S.A (ks.secret + m.mask ks.pid)) := by
  simp only [refreshShares, List.map_map, Function.comp_def, KeyShare.create]

/-- Helper: A distributes over addition (linearity).
    A(x + y) = A(x) + A(y) -/
lemma A_add (S : Scheme) (x y : S.Secret) :
    S.A (x + y) = S.A x + S.A y := by
  exact map_add S.A x y

/-- Helper: sum of mapped A equals A of sum (linearity over lists). -/
lemma sum_map_A (S : Scheme) (xs : List S.Secret) :
    (xs.map S.A).sum = S.A xs.sum := by
  induction xs with
  | nil => simp [map_zero]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, ← map_add]

/-- Well-formed KeyShare: pk_i = A(secret) -/
def KeyShare.wellFormed (S : Scheme) (ks : KeyShare S) : Prop :=
  ks.pk_i = S.A ks.secret

/-- Refresh preserves global pk: Σ pk'_i = Σ pk_i when Σ mask_i = 0.
    Uses linearity of A and zero-sum property.

    **Mathematical justification**:
    - For each share: pk'_i = A(sk_i + mask_i) = A(sk_i) + A(mask_i) = pk_i + A(mask_i)
    - Summing: Σ pk'_i = Σ pk_i + Σ A(mask_i)
    - By linearity: Σ A(mask_i) = A(Σ mask_i) = A(0) = 0
    - Therefore: Σ pk'_i = Σ pk_i

    Requires well-formed shares: each pk_i = A(sk_i). -/
lemma refresh_pk_unchanged
  (S : Scheme)
  (m : MaskFn S)
  (shares : List (KeyShare S))
  (hwf : ∀ ks ∈ shares, KeyShare.wellFormed S ks)
  (hsum : (shares.map (fun ks => m.mask ks.pid)).sum = 0) :
  let refreshed := refreshShares S m shares
  (refreshed.map (·.pk_i)).sum = (shares.map (·.pk_i)).sum := by
  simp only [refreshShares_pk_i_map]
  -- Rewrite A(sk + mask) = A(sk) + A(mask) for each element
  have heq : shares.map (fun ks => S.A (ks.secret + m.mask ks.pid)) =
             shares.map (fun ks => S.A ks.secret + S.A (m.mask ks.pid)) := by
    congr 1
    ext ks
    exact A_add S ks.secret (m.mask ks.pid)
  rw [heq]
  -- Use sum_map_add_eq from Sign.lean
  rw [IceNine.Proofs.Correctness.Sign.sum_map_add_eq]
  -- The A(mask) sum is A(Σ mask) = A(0) = 0
  have hmask_sum : (shares.map (fun ks => S.A (m.mask ks.pid))).sum = 0 := by
    -- Rewrite map to use composition: shares.map (S.A ∘ (fun ks => m.mask ks.pid))
    have hmap_comp : shares.map (fun ks => S.A (m.mask ks.pid)) =
                     (shares.map (fun ks => m.mask ks.pid)).map S.A := by
      simp only [List.map_map, Function.comp_def]
    rw [hmap_comp, sum_map_A, hsum, map_zero]
  rw [hmask_sum, add_zero]
  -- Remaining: show Σ A(sk) = Σ pk_i using well-formedness
  congr 1
  apply List.map_congr_left
  intro ks hks
  exact (hwf ks hks).symm

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

/-- Helper: when share senders match Sset, mapping over shares equals mapping over Sset. -/
lemma map_sender_eq_map_Sset
    (S : Scheme)
    (Sset : List S.PartyId)
    (shares : List (SignShareMsg S))
    (f : S.PartyId → S.Secret)
    (hpids : shares.map (·.sender) = Sset) :
    shares.map (fun sh => f sh.sender) = Sset.map f := by
  rw [← hpids]
  simp only [List.map_map, Function.comp_def]

/-- Rerandomization preserves signature using zero-sum masks.
    Zero-sum property is carried in the RerandMasks structure.

    The proof uses the zero-sum property from RerandMasks.shareSumZero
    and the sender-Sset correspondence to apply aggregateSignature_masks_zero. -/
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
  apply IceNine.Proofs.Correctness.Sign.aggregateSignature_masks_zero
  -- Need to show: (shares.map (fun sh => masks.shareMask sh.sender)).sum = 0
  -- Use map_sender_eq_map_Sset to convert to Sset.map masks.shareMask
  rw [map_sender_eq_map_Sset S Sset shares masks.shareMask hpids]
  -- Now apply the zero-sum property from RerandMasks
  exact masks.shareSumZero

end IceNine.Proofs.Extensions.RefreshRepair
