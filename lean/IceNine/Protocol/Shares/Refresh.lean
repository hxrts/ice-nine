/-
# Share Refresh via Zero-Sum Masks

Proactive security: periodically refresh shares to limit damage from
past compromises. Each party adds a random mask to its share. If masks
sum to zero over the active set, the global secret (and pk) is unchanged
but individual shares look completely new.

Key insight: Linearity of A means A(sk + m) = A(sk) + A(m), so pk_i changes
but Σ pk_i stays fixed when Σ m_i = 0.
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.State.Phase  -- for Join class

namespace IceNine.Protocol

open List

/-!
## Mask Functions

A mask function assigns a random-looking offset to each party's share.
Masks merge via pointwise addition (CRDT semilattice structure).
-/

/-- Mask function: maps party ID to a secret offset.
    Fresh masks are sampled such that they sum to zero. -/
structure MaskFn (S : Scheme) where
  mask : S.PartyId → S.Secret

/-- CRDT merge: pointwise addition of masks.
    Join of two refresh rounds = combined mask per party. -/
instance (S : Scheme) : Join (MaskFn S) :=
  ⟨fun a b => { mask := fun pid => a.mask pid + b.mask pid }⟩

/-!
## Zero-Sum Invariant

The critical property: masks sum to zero over the active participant set.
This ensures Σ sk_i remains unchanged, preserving the global secret.
-/

/-- Mask function with proof that masks sum to zero on active set.
    The invariant guarantees global secret is preserved. -/
structure ZeroSumMaskFn (S : Scheme) (active : Finset S.PartyId) where
  fn       : MaskFn S
  sum_zero : (active.toList.map (fun pid => fn.mask pid)).sum = 0

/-- Merge preserves zero-sum: (a+b).sum = a.sum + b.sum = 0 + 0 = 0. -/
instance (S : Scheme) (active : Finset S.PartyId) : Join (ZeroSumMaskFn S active) :=
  ⟨fun a b =>
    { fn := { mask := fun pid => a.fn.mask pid + b.fn.mask pid }
    , sum_zero := by
        simp only [List.map_map, List.sum_map_add]; simp [a.sum_zero, b.sum_zero] }⟩

/-!
## Refresh Operation

Apply masks to shares. Each party's share is updated:
  sk'_i = sk_i + m_i
  pk'_i = A(sk'_i) = A(sk_i) + A(m_i)
Global pk = Σ pk'_i = Σ pk_i + A(Σ m_i) = Σ pk_i (since Σ m_i = 0).
-/

/-- Apply masks to shares, recompute public shares via A.
    Zero-sum masks preserve global pk = Σ pk_i. -/
def refreshShares
  (S : Scheme)
  (m : MaskFn S)
  (shares : List (KeyShare S)) : List (KeyShare S) :=
  shares.map (fun ks =>
    -- Add mask to secret share
    let sk' := ks.secret + m.mask ks.pid
    -- Recompute public share from new secret
    let pk' := S.A sk'
    -- Create new KeyShare with wrapped secret
    KeyShare.create S ks.pid sk' pk' ks.pk)

end IceNine.Protocol
