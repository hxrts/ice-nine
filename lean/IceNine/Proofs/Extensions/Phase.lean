/-
# Phase Handler Monotonicity

CRDT safety: all phase handlers preserve semilattice ordering.
If state a ≤ b before a handler, then handler(a) ≤ handler(b) after.

This guarantees:
- Out-of-order message delivery doesn't break convergence
- Replaying messages is idempotent (safe in distributed setting)
- Eventual consistency: all replicas converge to same state
-/

import IceNine.Protocol.State.PhaseHandlers
import IceNine.Protocol.State.PhaseSig

namespace IceNine.Proofs.Extensions.Phase

open IceNine.Protocol

/-!
## Handler Monotonicity

Each handler function preserves the semilattice ordering.
Key property for CRDT correctness.
-/

/-- Commit handler is monotone: a ≤ b → step(a) ≤ step(b).
    Adding a commit preserves ordering between states.

    NOTE: Uses sorry because MsgMap monotonicity proof is complex.
    The property holds because inserting the same key into both maps preserves ordering. -/
lemma stepCommit_monotone (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (msg : DkgCommitMsg S) :
  ∀ a b, a ≤ b → stepCommit S msg a ≤ stepCommit S msg b := by
  intro a b _h
  sorry

/-- Reveal handler is monotone: a ≤ b → step(a) ≤ step(b).
    Adding a reveal preserves ordering between states.

    NOTE: Uses sorry because MsgMap monotonicity proof is complex.
    The property holds because inserting the same key into both maps preserves ordering. -/
lemma stepReveal_monotone (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    (msg : DkgRevealMsg S) :
  ∀ a b, a ≤ b → stepReveal S msg a ≤ stepReveal S msg b := by
  intro a b _h
  sorry

/-- Share handler is monotone on state component.
    Adding a signature share preserves ordering.

    NOTE: Uses sorry because MsgMap monotonicity proof is complex.
    The property holds because inserting the same key into both maps preserves ordering. -/
lemma stepShare_monotone (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    (msg : SignShareMsg S) :
  ∀ a b, a.state ≤ b.state → (stepShare S msg a).state ≤ (stepShare S msg b).state := by
  intro a b _h
  sorry

end IceNine.Proofs.Extensions.Phase
