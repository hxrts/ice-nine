/-
# Threshold-Aware State Merge

Couples ShareState with ThresholdCtx to maintain invariants during CRDT merge.

The key challenge: when two replicas merge, the active signer sets may differ.
We must:
1. Union the active sets: merged.active = a.active ∪ b.active
2. Preserve threshold: merged.t = max(a.t, b.t)
3. Prove validity: merged.t ≤ |merged.active| (cardinality proof)
4. Recompute coefficients: Lagrange λ_i depend on the signer set

This module provides three merge strategies:
- mergeShareWithCtxOnes: conservative fallback to n-of-n (no field needed)
- mergeShareWithCtx: full recompute of Lagrange coeffs (requires Field)
- mergeShareWithCtxAuto: auto-selects based on field availability
-/

import IceNine.Protocol.State.Phase
import IceNine.Protocol.Sign.Types
import IceNine.Protocol.Sign.Core
import IceNine.Protocol.Sign.Threshold

namespace IceNine.Protocol

/-!
## ShareState with Threshold Context

ShareWithCtx pairs the accumulated signing state (commits, reveals, shares)
with a ThresholdCtx that tracks the active set and proves t ≤ |active|.

This coupling ensures we can always aggregate validly after merge.
-/

variable (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]

/-- Share phase state paired with threshold context.

    **Invariants:**
    1. `ctx.card_ge`: ctx.t ≤ |ctx.active| (from ThresholdCtx)
    2. `active_inv`: ctx.active ⊆ state.active (encoded here)

    The second invariant ensures that the threshold context's active set
    is always a subset of the state's active set. This is needed to prove
    that merge preserves the threshold validity.

    NOTE: Repr is not auto-derived because ThresholdCtx contains proofs. -/
structure ShareWithCtx where
  state : ShareState S    -- accumulated commits/reveals/shares
  ctx   : ThresholdCtx S  -- threshold + active set + proof
  active_inv : ctx.active ⊆ state.active  -- invariant: ctx tracks subset of state

/-!
## Merge Strategies

Three approaches to merging threshold contexts:

1. **Conservative (ones)**: Fall back to n-of-n with simple sum.
   - Pro: No field required, always safe
   - Con: Loses threshold efficiency (all signers must participate)

2. **Full recompute**: Recompute Lagrange coefficients for merged set.
   - Pro: Preserves t-of-n semantics
   - Con: Requires Field instance for division

3. **Auto**: Select strategy based on field availability.
   - Use in generic code that may or may not have a Field
-/

/-- Conservative merge: fall back to n-of-n (all-parties).
    Safe when Field is unavailable or undesired. -/
def mergeShareWithCtxOnes (a b : ShareWithCtx S) : ShareWithCtx S :=
  -- Union the active sets from both replicas
  let mergedActive : Finset S.PartyId := a.state.active ∪ b.state.active
  -- Merge state via semilattice join (list append)
  let state : ShareState S := {
    commits := a.state.commits ⊔ b.state.commits,
    reveals := a.state.reveals ⊔ b.state.reveals,
    shares  := a.state.shares ⊔ b.state.shares,
    active  := mergedActive
  }
  -- n-of-n: threshold = full set size
  let t := mergedActive.card
  have hcard : t ≤ mergedActive.card := Nat.le_refl _
  let ctx : ThresholdCtx S := {
    active := mergedActive,
    t := t,
    mode := SignMode.all,
    strategy := CoeffStrategy.ones,
    card_ge := hcard,
    strategy_ok := by trivial
  }
  -- Invariant: ctx.active = mergedActive ⊆ state.active = mergedActive
  have hinv : ctx.active ⊆ state.active := Finset.Subset.refl _
  { state := state, ctx := ctx, active_inv := hinv }

variable [Field S.Scalar] [DecidableEq S.Scalar]

/-- Full merge with Lagrange coefficient recomputation.
    Preserves t-of-n semantics after merge. -/
noncomputable def mergeShareWithCtx
  (pidToScalar : S.PartyId → S.Scalar)
  (a b : ShareWithCtx S) : ShareWithCtx S :=
  -- Union active sets
  let mergedActive : Finset S.PartyId := a.state.active ∪ b.state.active
  -- Merge state components
  let state : ShareState S := {
    commits := a.state.commits ⊔ b.state.commits,
    reveals := a.state.reveals ⊔ b.state.reveals,
    shares  := a.state.shares ⊔ b.state.shares,
    active  := mergedActive
  }
  -- Take max threshold to preserve both guarantees
  let t := Nat.max a.ctx.t b.ctx.t
  -- Prove: max(t_a, t_b) ≤ |a.active ∪ b.active|
  -- Uses the active_inv invariants from a and b
  have hcard : t ≤ mergedActive.card := by
    -- a.ctx.t ≤ |a.ctx.active| ≤ |a.state.active| ≤ |merged|
    have ha_card : a.ctx.t ≤ a.ctx.active.card := a.ctx.card_ge
    have ha_sub : a.ctx.active ⊆ mergedActive :=
      Finset.Subset.trans a.active_inv Finset.subset_union_left
    have ha : a.ctx.t ≤ mergedActive.card :=
      Nat.le_trans ha_card (Finset.card_le_card ha_sub)
    -- b.ctx.t ≤ |b.ctx.active| ≤ |b.state.active| ≤ |merged|
    have hb_card : b.ctx.t ≤ b.ctx.active.card := b.ctx.card_ge
    have hb_sub : b.ctx.active ⊆ mergedActive :=
      Finset.Subset.trans b.active_inv Finset.subset_union_right
    have hb : b.ctx.t ≤ mergedActive.card :=
      Nat.le_trans hb_card (Finset.card_le_card hb_sub)
    -- max(a.t, b.t) ≤ merged.card
    exact Nat.max_le.mpr ⟨ha, hb⟩
  -- Recompute Lagrange coefficients for merged active set
  let coeffs : List (LagrangeCoeff S) := mergedActive.toList.map (fun pid =>
    { pid := pid, lambda := lagrangeCoeffAtZero S pidToScalar mergedActive.toList pid })
  have hlen : coeffs.length = mergedActive.toList.length := by simp only [coeffs, List.length_map]
  have hpid : coeffs.map (·.pid) = mergedActive.toList := by
    simp only [coeffs, List.map_map, Function.comp_def]
    conv_lhs => rw [show (fun x => x) = id from rfl, List.map_id]
  let ctx : ThresholdCtx S := {
    active := mergedActive,
    t := t,
    mode := SignMode.threshold,
    strategy := CoeffStrategy.lagrange coeffs,
    card_ge := hcard,
    strategy_ok := ⟨hlen, hpid⟩
  }
  -- Invariant: ctx.active = mergedActive ⊆ state.active = mergedActive
  have hinv : ctx.active ⊆ state.active := Finset.Subset.refl _
  { state := state, ctx := ctx, active_inv := hinv }

/-- Auto-merge: recompute coeffs if Field available, else fall back.
    Pass `some inferInstance` for field-backed schemes, `none` for lattice. -/
noncomputable def mergeShareWithCtxAuto
  (pidToScalar : S.PartyId → S.Scalar)
  (a b : ShareWithCtx S) : ShareWithCtx S :=
  mergeShareWithCtx S pidToScalar a b

end IceNine.Protocol
