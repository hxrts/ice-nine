/-
# Threshold-Aware Merge Soundness

Soundness proofs for threshold-aware CRDT merge operations.

When two replicas merge ShareState, the active signer sets may differ.
The merge must:
1. Union the active sets: merged.active = a.active ∪ b.active
2. Preserve threshold: merged.t = max(a.t, b.t)
3. Prove validity: merged.t ≤ |merged.active|
4. Recompute Lagrange coefficients for the merged set

## Design

The `ShareWithCtx` structure includes an `active_inv` field that encodes
the invariant `ctx.active ⊆ state.active`. This allows the merge functions
to prove threshold validity directly.

The proofs are inline in the definitions (Protocol/Sign/ThresholdMerge.lean).
This file provides additional theorems about merge properties.
-/

import IceNine.Protocol.Sign.ThresholdMerge
import Mathlib

namespace IceNine.Proofs.Soundness.ThresholdMerge

open IceNine.Protocol

variable (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]

/-!
## Merge Strategy Properties

These theorems document the key properties of the merge operations.
All proofs are complete thanks to the `active_inv` invariant.
-/

/-- Conservative merge preserves threshold validity.
    Since t = |active|, we have t ≤ |active| by reflexivity. -/
theorem conservative_merge_valid (a b : ShareWithCtx S) :
    let merged := mergeShareWithCtxOnes S a b
    merged.ctx.t ≤ merged.ctx.active.card := by
  simp only [mergeShareWithCtxOnes]
  exact Nat.le_refl _

/-- Conservative merge preserves the active_inv invariant. -/
theorem conservative_merge_preserves_inv (a b : ShareWithCtx S) :
    let merged := mergeShareWithCtxOnes S a b
    merged.ctx.active ⊆ merged.state.active := by
  simp only [mergeShareWithCtxOnes]
  exact Finset.Subset.refl _

/-- Full merge unions active sets correctly. -/
theorem full_merge_unions_active [Field S.Scalar] [DecidableEq S.Scalar]
    (pidToScalar : S.PartyId → S.Scalar)
    (a b : ShareWithCtx S) :
    let merged := mergeShareWithCtx S pidToScalar a b
    merged.state.active = a.state.active ∪ b.state.active := by
  simp only [mergeShareWithCtx]

/-- Full merge takes max threshold. -/
theorem full_merge_max_threshold [Field S.Scalar] [DecidableEq S.Scalar]
    (pidToScalar : S.PartyId → S.Scalar)
    (a b : ShareWithCtx S) :
    let merged := mergeShareWithCtx S pidToScalar a b
    merged.ctx.t = Nat.max a.ctx.t b.ctx.t := by
  simp only [mergeShareWithCtx]

/-- Full merge preserves the active_inv invariant. -/
theorem full_merge_preserves_inv [Field S.Scalar] [DecidableEq S.Scalar]
    (pidToScalar : S.PartyId → S.Scalar)
    (a b : ShareWithCtx S) :
    let merged := mergeShareWithCtx S pidToScalar a b
    merged.ctx.active ⊆ merged.state.active := by
  simp only [mergeShareWithCtx]
  exact Finset.Subset.refl _

/-!
## Cardinality Lemma (Standalone)

This lemma is proved inline in `mergeShareWithCtx` using the `active_inv` invariant.
We provide a standalone version for reference and reuse.
-/

/-- Cardinality lemma: max threshold ≤ merged cardinality.
    This is the core property that enables threshold-preserving merge. -/
theorem max_threshold_le_merged_card
    (a b : ShareWithCtx S) :
    Nat.max a.ctx.t b.ctx.t ≤ (a.state.active ∪ b.state.active).card := by
  -- a.ctx.t ≤ |a.ctx.active| ≤ |a.state.active| ≤ |merged|
  have ha_card : a.ctx.t ≤ a.ctx.active.card := a.ctx.card_ge
  have ha_sub : a.ctx.active ⊆ a.state.active ∪ b.state.active :=
    Finset.Subset.trans a.active_inv Finset.subset_union_left
  have ha_merged : a.ctx.active.card ≤ (a.state.active ∪ b.state.active).card :=
    Finset.card_le_card ha_sub
  have ha : a.ctx.t ≤ (a.state.active ∪ b.state.active).card :=
    Nat.le_trans ha_card ha_merged
  -- Similarly for b
  have hb_card : b.ctx.t ≤ b.ctx.active.card := b.ctx.card_ge
  have hb_sub : b.ctx.active ⊆ a.state.active ∪ b.state.active :=
    Finset.Subset.trans b.active_inv Finset.subset_union_right
  have hb_merged : b.ctx.active.card ≤ (a.state.active ∪ b.state.active).card :=
    Finset.card_le_card hb_sub
  have hb : b.ctx.t ≤ (a.state.active ∪ b.state.active).card :=
    Nat.le_trans hb_card hb_merged
  -- max(a.t, b.t) ≤ merged.card
  exact Nat.max_le.mpr ⟨ha, hb⟩

end IceNine.Proofs.Soundness.ThresholdMerge
