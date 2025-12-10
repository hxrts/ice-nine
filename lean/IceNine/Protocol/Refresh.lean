/-
# Share refresh/removal via zero-sum masks

We rerandomize long-term shares with a mask function whose sum over the active
participants is zero. Because A is linear, the global pk stays unchanged while
each party receives a fresh-looking share.
-/

import IceNine.Protocol.Core

namespace IceNine.Protocol

open List

/-- Mask function keyed by participant id. -/
structure MaskFn (S : Scheme) :=
  (mask : S.PartyId → S.Secret)

instance (S : Scheme) : Join (MaskFn S) :=
  ⟨fun a b => { mask := fun pid => a.mask pid + b.mask pid }⟩

-- Zero-sum invariant on a given active set.
structure ZeroSumMaskFn (S : Scheme) (active : Finset S.PartyId) :=
  (fn : MaskFn S)
  (sum_zero : (active.toList.map (fun pid => fn.mask pid)).sum = 0)

-- Merge of zero-sum masks preserves zero-sum on the same active set.
instance (S : Scheme) (active : Finset S.PartyId) : Join (ZeroSumMaskFn S active) :=
  ⟨fun a b =>
    { fn := { mask := fun pid => a.fn.mask pid + b.fn.mask pid }
    , sum_zero := by
        simp [List.map_map, add_comm, add_left_comm, add_assoc, a.sum_zero, b.sum_zero] }⟩

/-- Apply masks to shares; recompute pk_i with the linear map A. -/
def refreshShares
  (S : Scheme)
  (m : MaskFn S)
  (shares : List (KeyShare S)) : List (KeyShare S) :=
  shares.map (fun ks =>
    let sk' := ks.sk_i + m.mask ks.pid
    let pk' := S.A sk'
    { ks with sk_i := sk', pk_i := pk' })

end IceNine.Protocol
