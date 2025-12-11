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
import IceNine.Protocol.Sign.Sign

namespace IceNine.Protocol

/-!
## ShareState with Threshold Context

ShareWithCtx pairs the accumulated signing state (commits, reveals, shares)
with a ThresholdCtx that tracks the active set and proves t ≤ |active|.

This coupling ensures we can always aggregate validly after merge.
-/

/-- Share phase state paired with threshold context.
    Invariant: ctx.card_ge proves ctx.t ≤ |ctx.active|. -/
structure ShareWithCtx (S : Scheme) [DecidableEq S.PartyId] :=
  (state : ShareState S)    -- accumulated commits/reveals/shares
  (ctx   : ThresholdCtx S)  -- threshold + active set + proof
deriving Repr

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
def mergeShareWithCtxOnes (S : Scheme) [DecidableEq S.PartyId]
  (a b : ShareWithCtx S) : ShareWithCtx S :=
  -- Union the active sets from both replicas
  let mergedActive := a.state.active ∪ b.state.active
  -- Merge state via semilattice join (list append)
  let state := { commits := a.state.commits ⊔ b.state.commits,
                 reveals := a.state.reveals ⊔ b.state.reveals,
                 shares  := a.state.shares ⊔ b.state.shares,
                 active  := mergedActive }
  -- n-of-n: threshold = full set size
  let t := mergedActive.card
  have hcard : t ≤ mergedActive.card := by simp
  let ctx : ThresholdCtx S :=
    { active := mergedActive,
      t := t,
      mode := SignMode.all,
      strategy := CoeffStrategy.ones,
      card_ge := hcard,
      strategy_ok := by trivial }
  { state := state, ctx := ctx }

/-- Full merge with Lagrange coefficient recomputation.
    Preserves t-of-n semantics after merge. -/
def mergeShareWithCtx
  (S : Scheme) [Field S.Scalar] [DecidableEq S.PartyId]
  (pidToScalar : S.PartyId → S.Scalar)
  (a b : ShareWithCtx S) : ShareWithCtx S :=
  -- Union active sets
  let mergedActive := a.state.active ∪ b.state.active
  -- Merge state components
  let state := { commits := a.state.commits ⊔ b.state.commits,
                 reveals := a.state.reveals ⊔ b.state.reveals,
                 shares  := a.state.shares ⊔ b.state.shares,
                 active  := mergedActive }
  -- Take max threshold to preserve both guarantees
  let t := Nat.max a.ctx.t b.ctx.t
  -- Prove: max(t_a, t_b) ≤ |a.active ∪ b.active|
  have ha : a.ctx.t ≤ mergedActive.card :=
    le_trans a.ctx.card_ge (by exact Finset.card_mono (by exact Finset.subset_union_left))
  have hb : b.ctx.t ≤ mergedActive.card :=
    le_trans b.ctx.card_ge (by exact Finset.card_mono (by exact Finset.subset_union_right))
  have hcard : t ≤ mergedActive.card := by
    apply Nat.max_le_iff.mpr; exact ⟨ha, hb⟩
  -- Recompute Lagrange coefficients for merged active set
  let coeffs := mergedActive.toList.map (fun pid =>
    { pid := pid, lambda := lagrangeCoeffAtZero S pidToScalar mergedActive.toList pid })
  have hlen : coeffs.length = mergedActive.toList.length := by simp
  have hpid : coeffs.map (·.pid) = mergedActive.toList := by simp
  let ctx : ThresholdCtx S :=
    { active := mergedActive,
      t := t,
      mode := SignMode.threshold,
      strategy := CoeffStrategy.lagrange coeffs,
      card_ge := hcard,
      strategy_ok := by simp [strategyOK, hpid, hlen] }
  { state := state, ctx := ctx }

/-- Auto-merge: recompute coeffs if Field available, else fall back.
    Pass `some inferInstance` for field-backed schemes, `none` for lattice. -/
def mergeShareWithCtxAuto
  (S : Scheme) [DecidableEq S.PartyId]
  (fieldInst : Option (Field S.Scalar))
  (pidToScalar : S.PartyId → S.Scalar)
  (a b : ShareWithCtx S) : ShareWithCtx S :=
  match fieldInst with
  | none      => mergeShareWithCtxOnes S a b
  | some inst =>
      -- Install field instance and use full merge
      let _inst : Field S.Scalar := inst
      mergeShareWithCtx S pidToScalar a b

end IceNine.Protocol
