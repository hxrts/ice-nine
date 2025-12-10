/-
# Phase Handler Monotonicity

CRDT safety: all phase handlers preserve semilattice ordering.
If state a ≤ b before a handler, then handler(a) ≤ handler(b) after.

This guarantees:
- Out-of-order message delivery doesn't break convergence
- Replaying messages is idempotent (safe in distributed setting)
- Eventual consistency: all replicas converge to same state
-/

import IceNine.Protocol.PhaseHandlers
import IceNine.Protocol.PhaseSig

namespace IceNine.Security.Phase

open IceNine.Protocol

/-!
## Handler Monotonicity

Each handler function preserves the semilattice ordering.
Key property for CRDT correctness.
-/

/-- Commit handler is monotone: a ≤ b → step(a) ≤ step(b).
    Adding a commit preserves ordering between states. -/
lemma stepCommit_monotone (S : Scheme) (msg : DkgCommitMsg S) :
  ∀ a b, a ≤ b → stepCommit S msg a ≤ stepCommit S msg b := by
  intro a b h; exact h

/-- Reveal handler is monotone: a ≤ b → step(a) ≤ step(b).
    Adding a reveal preserves ordering between states. -/
lemma stepReveal_monotone (S : Scheme) (msg : DkgRevealMsg S) :
  ∀ a b, a ≤ b → stepReveal S msg a ≤ stepReveal S msg b := by
  intro a b h; exact h

/-- Share handler is monotone on state component.
    Adding a signature share preserves ordering. -/
lemma stepShare_monotone (S : Scheme) [DecidableEq S.PartyId] (msg : SignShareMsg S) :
  ∀ a b, a.state ≤ b.state → (stepShare S msg a).state ≤ (stepShare S msg b).state := by
  intro a b h; exact h

end IceNine.Security.Phase
