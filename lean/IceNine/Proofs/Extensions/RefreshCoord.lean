/-
# Refresh Coordination Proofs

Lemmas for constructing zero-sum masks in the refresh coordination protocol.

Separated from Protocol/Shares/RefreshCoord.lean to maintain protocol/proof separation.
-/

import IceNine.Protocol.Shares.RefreshCoord
import Mathlib

open scoped BigOperators

set_option autoImplicit false

namespace IceNine.Proofs.Extensions.RefreshCoord

open IceNine.Protocol.RefreshCoord
open IceNine.Protocol

/-!
## Mask Function Correctness

Proofs that the constructed mask function matches the computed final masks.
-/

/-- Prove mask function equals computed masks.

    This theorem connects the computed masks list with the mask function,
    enabling proof that the zero-sum property holds. -/
theorem makeMaskFn_eq_finalMasks (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    (st : RefreshRoundState S) (masks : List S.Secret) (maskFn : MaskFn S)
    (hmaskFn : makeMaskFn S st = .ok maskFn)
    (hmasks : computeFinalMasks S st = .ok masks) :
    st.parties.map (fun pid => maskFn.mask pid) = masks := by
  unfold computeFinalMasks at hmasks
  unfold makeMaskFn at hmaskFn
  cases hadj : st.adjustment with
  | none =>
    -- Impossible: adjustment = none means computeFinalMasks throws error
    simp only [hadj] at hmasks
    exact Except.noConfusion hmasks
  | some adj =>
    simp only [hadj] at hmasks hmaskFn ⊢
    cases hcoord : st.coordinator with
    | error e =>
      -- Impossible: coordinator = error means computeFinalMasks throws error
      simp only [hcoord, Except.mapError] at hmasks
      exact Except.noConfusion hmasks
    | ok coord =>
      simp only [hcoord] at hmaskFn hmasks
      injection hmaskFn with hfn
      injection hmasks with heq
      rw [← hfn, ← heq]

/-!
## List Nodup Lemmas
-/

/-- For a nodup list, count of any member is 1. -/
lemma nodup_count_eq_one {α : Type*} [DecidableEq α]
    {l : List α} (hnodup : l.Nodup) {x : α} (hx : x ∈ l.toFinset) :
    l.count x = 1 := by
  rw [List.mem_toFinset] at hx
  exact List.count_eq_one_of_mem hnodup hx

/-!
## Zero-Sum Proof Construction

The main theorem for constructing zero-sum mask proofs from runtime checks.
-/

/-- Derive zero-sum proof from runtime checks.

    This uses the fact that for nodup lists, toFinset.toList is a permutation.
    The proof combines:
    1. Mask function correctness (makeMaskFn_eq_finalMasks)
    2. Permutation invariance of sum
    3. Runtime zero-sum check -/
theorem constructZeroSumMask_proof (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    (st : RefreshRoundState S)
    (masks : List S.Secret) (maskFn : MaskFn S)
    (hmaskFn : makeMaskFn S st = .ok maskFn)
    (hmasks : computeFinalMasks S st = .ok masks)
    (hzero : masks.sum = 0)
    (hnodup : st.parties.Nodup) :
    st.parties.toFinset.sum (fun pid => maskFn.mask pid) = 0 := by
  have heq := makeMaskFn_eq_finalMasks S st masks maskFn hmaskFn hmasks
  -- For nodup lists, toFinset.toList is a permutation of the original list
  have hperm : List.Perm st.parties.toFinset.toList st.parties := List.toFinset_toList hnodup
  -- Map preserves permutations
  have hperm_map : List.Perm (st.parties.toFinset.toList.map (fun pid => maskFn.mask pid))
                            (st.parties.map (fun pid => maskFn.mask pid)) :=
    hperm.map (fun pid => maskFn.mask pid)
  -- Sum is invariant under permutation
  have hsum_list : (st.parties.toFinset.toList.map (fun pid => maskFn.mask pid)).sum = 0 := by
    simpa [hperm_map.sum_eq, heq] using hzero
  classical
  simpa [Finset.sum_toList] using hsum_list

end IceNine.Proofs.Extensions.RefreshCoord
