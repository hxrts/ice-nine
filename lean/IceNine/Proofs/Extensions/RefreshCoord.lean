/-
# Refresh Coordination Proofs

Soundness proofs for the distributed refresh coordination protocol.

## Key Theorems

1. `verifyZeroSum_spec`: Boolean verification reflects the Prop
2. `makeMaskFn_eq_finalMasks`: Mask function matches computed mask list
3. `List.sum_perm`: Sum is invariant under permutation
4. `List.toFinset_toList_perm'`: toFinset.toList permutes to original

The refresh coordination protocol ensures that multiple parties can
generate zero-sum masks without a trusted coordinator, enabling
proactive security through periodic share refresh.
-/

import IceNine.Protocol.Shares.RefreshCoord
import Mathlib

set_option autoImplicit false

namespace IceNine.Proofs.Extensions.RefreshCoord

open IceNine.Protocol.RefreshCoord
open IceNine.Protocol

/-!
## Zero-Sum Verification
-/

/-- verifyZeroSum reflects zeroSumProp.
    The boolean check is equivalent to the propositional statement. -/
theorem verifyZeroSum_spec (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    [Inhabited S.PartyId] [DecidableEq S.Secret]
    (st : RefreshRoundState S) :
    verifyZeroSum S st = true ↔ zeroSumProp S st := by
  unfold verifyZeroSum zeroSumProp
  split <;> simp_all [decide_eq_true_iff]

/-!
## List Permutation Lemmas
-/

/-- Sum is invariant under list permutation. -/
theorem List.sum_perm {α : Type*} [AddCommMonoid α] (l1 l2 : List α) :
    l1.Perm l2 → l1.sum = l2.sum := by
  intro hperm; exact hperm.sum_eq

/-- Converting list to finset and back gives a permutation of the original. -/
theorem List.toFinset_toList_perm' {α : Type*} [DecidableEq α] (l : List α) :
    l.Nodup → l.toFinset.toList.Perm l := by
  intro hnodup
  exact List.toFinset_toList hnodup

/-!
## Mask Function Correctness
-/

/-- The mask function applied to parties equals the computed mask list (on success).

    **Mathematical justification**:
    Both `makeMaskFn` and `computeFinalMasks` use identical logic:
    - For each party pid, return `adj.adjustment` if pid is coordinator, else `r.mask`
    - Default to 0 if no reveal exists

    The only difference is that `computeFinalMasks` maps over `st.parties` explicitly
    while `makeMaskFn` returns a function. When we map the function over parties,
    we get the same list.

    **Proof**: Case split on `st.adjustment`:
    - `none`: `computeFinalMasks` throws, contradicting `hmasks`
    - `some adj`: Both definitions use identical logic, so the maps are equal -/
theorem makeMaskFn_eq_finalMasks (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S) (masks : List S.Secret)
    (hmasks : computeFinalMasks S st = .ok masks) :
    st.parties.map (fun pid => (makeMaskFn S st).mask pid) = masks := by
  unfold computeFinalMasks at hmasks
  unfold makeMaskFn
  cases hadj : st.adjustment with
  | none => simp only [hadj] at hmasks
  | some adj =>
    simp only [hadj] at hmasks ⊢
    injection hmasks with heq
    exact heq.symm

/-!
## Zero-Sum Mask Construction

The `constructZeroSumMask` function in Protocol takes a proof parameter `hsum`
that the mask function sums to zero. This theorem provides that proof when
the preconditions are satisfied.

**Proof strategy**:
1. Use `makeMaskFn_eq_finalMasks` to show the mask function maps to `masks`
2. Use `List.sum_toFinset` to convert list sum to finset sum
3. Chain: finset sum = list sum = masks.sum = 0

**Usage**: Call this theorem to construct the proof parameter for
`constructZeroSumMask` when you have `hmasks`, `hzero`, and `hnodup`.
-/

/-- Zero-sum property: when masks are valid, finset sum equals zero.

    This theorem provides the proof obligation for `constructZeroSumMask`.

    **Usage**:
    ```
    let hsum := constructZeroSumMask_obligation S st masks hmasks hzero hnodup
    let zeroSumMask := constructZeroSumMask S st hsum
    ```
-/
theorem constructZeroSumMask_obligation (S : Scheme)
    [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] [Inhabited S.PartyId]
    (st : RefreshRoundState S)
    (masks : List S.Secret)
    (hmasks : computeFinalMasks S st = .ok masks)
    (hzero : masks.sum = 0)
    (hnodup : st.parties.Nodup) :
    st.parties.toFinset.sum (makeMaskFn S st).mask = 0 := by
  -- Step 1: Show makeMaskFn maps to same values as computeFinalMasks
  have heq := makeMaskFn_eq_finalMasks S st masks hmasks
  -- Step 2: finset.sum f = list.sum (list.map f) when nodup
  -- Using: Finset.sum_toList and List.toFinset_toList
  have hperm : st.parties.toFinset.toList.Perm st.parties :=
    List.toFinset_toList hnodup
  -- The finset sum equals the list sum over toList
  rw [Finset.sum_toList]
  -- toList.map f has same sum as parties.map f (by permutation)
  have hmap_perm : (st.parties.toFinset.toList.map (makeMaskFn S st).mask).Perm
                   (st.parties.map (makeMaskFn S st).mask) :=
    List.Perm.map _ hperm
  rw [hmap_perm.sum_eq]
  -- Step 3: Chain to zero via heq
  rw [heq, hzero]

end IceNine.Proofs.Extensions.RefreshCoord
