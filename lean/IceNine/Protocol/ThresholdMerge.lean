/-
# Threshold-aware merge wrapper

Couple a ShareState with a ThresholdCtx to ensure merges keep active sets and
threshold proofs aligned.
-/

import IceNine.Protocol.Phase
import IceNine.Protocol.Sign

namespace IceNine.Protocol

structure ShareWithCtx (S : Scheme) :=
  (state : ShareState S)
  (ctx   : ThresholdCtx S)

def mergeShareWithCtx (S : Scheme) [DecidableEq S.PartyId]
  (a b : ShareWithCtx S) : ShareWithCtx S :=
  let mergedActive := a.state.active ∪ b.state.active
  let state := { commits := a.state.commits ⊔ b.state.commits,
                 reveals := a.state.reveals ⊔ b.state.reveals,
                 shares  := a.state.shares ⊔ b.state.shares,
                 active  := mergedActive }
  let t := Nat.max a.ctx.t b.ctx.t
  have hcard : t ≤ mergedActive.card := by
    have ha : a.ctx.t ≤ mergedActive.card :=
      le_trans a.ctx.card_ge (by exact Finset.card_mono (by exact Finset.subset_union_left))
    have hb : b.ctx.t ≤ mergedActive.card :=
      le_trans b.ctx.card_ge (by exact Finset.card_mono (by exact Finset.subset_union_right))
    exact le_trans (Nat.le_max_left _ _) ha ▸ le_trans (Nat.le_max_right _ _) hb
  let ctx := { active := mergedActive, t := t, card_ge := hcard }
  { state := state, ctx := ctx }

end IceNine.Protocol
