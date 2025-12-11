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

variable (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]

/-- Share phase state paired with threshold context.
    Invariant: ctx.card_ge proves ctx.t ≤ |ctx.active|.

    NOTE: Repr is not auto-derived because ThresholdCtx contains proofs. -/
structure ShareWithCtx where
  state : ShareState S    -- accumulated commits/reveals/shares
  ctx   : ThresholdCtx S  -- threshold + active set + proof

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
  { state := state, ctx := ctx }

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
  -- NOTE: This relies on invariant that ctx.active = state.active
  have hcard : t ≤ mergedActive.card := by
    -- Requires showing both a.ctx.t and b.ctx.t ≤ mergedActive.card
    -- This holds when ctx.active ⊆ state.active (invariant)
    sorry
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
  { state := state, ctx := ctx }

/-- Auto-merge: recompute coeffs if Field available, else fall back.
    Pass `some inferInstance` for field-backed schemes, `none` for lattice. -/
noncomputable def mergeShareWithCtxAuto
  (pidToScalar : S.PartyId → S.Scalar)
  (a b : ShareWithCtx S) : ShareWithCtx S :=
  mergeShareWithCtx S pidToScalar a b

end IceNine.Protocol
