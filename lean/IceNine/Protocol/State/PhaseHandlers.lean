/-
# Phase Handlers

Monotone handlers for CRDT-safe state transitions. Each handler:
- Adds data to the current phase state
- Preserves semilattice ordering (a ≤ handler(a))
- Enables merge of divergent execution traces

Key property: handler(a ⊔ b) = handler(a) ⊔ handler(b)
This ensures CRDT convergence regardless of message order.
-/

import IceNine.Protocol.State.Phase
import IceNine.Protocol.DKG.Core
import IceNine.Protocol.DKG.Threshold
import IceNine.Protocol.Sign.Sign
import IceNine.Protocol.Sign.ThresholdMerge

namespace IceNine.Protocol

open List

/-!
## Commit Phase Handler

Add commitment messages. Uses append (⊔) for monotonic update.
-/

/-- Add a commit message to commit phase state.
    Monotone: st ≤ stepCommit(st, msg). -/
def stepCommit
  (S : Scheme)
  (msg : DkgCommitMsg S)
  (st  : CommitState S) : CommitState S :=
{ commits := st.commits ⊔ [msg] }

/-!
## Reveal Phase Handler

Add reveal messages. Commits are preserved, reveals are appended.
-/

/-- Add a reveal message to reveal phase state.
    Monotone: st ≤ stepReveal(st, msg). -/
def stepReveal
  (S : Scheme)
  (msg : DkgRevealMsg S)
  (st  : RevealState S) : RevealState S :=
{ commits := st.commits, reveals := st.reveals ⊔ [msg] }

/-!
## Share Phase Handler

Add signature shares. Active set and threshold context preserved.
-/

/-- Add a signature share to share phase state.
    Monotone: st ≤ stepShare(st, msg). -/
def stepShare
  (S : Scheme) [DecidableEq S.PartyId]
  (msg : SignShareMsg S)
  (st  : ShareWithCtx S) : ShareWithCtx S :=
-- Append share to list, preserve everything else
let st' : ShareState S := { commits := st.state.commits,
                            reveals := st.state.reveals,
                            shares  := st.state.shares ⊔ [msg],
                            active  := st.state.active }
⟨st', st.ctx⟩

/-!
## Finalization

Attempt to produce final signature when threshold of shares collected.
-/

/-- Try to aggregate into final signature.
    Succeeds only if all shares are from declared active set. -/
def tryAggregate
  (S : Scheme) [DecidableEq S.PartyId]
  (swc : ShareWithCtx S)
  (challenge : S.Challenge)
  : Option (DoneState S) :=
  let ctx := swc.ctx
  let st  := swc.state
  -- Check all shares come from active signers
  if hfrom : ∀ sh ∈ st.shares, sh.sender ∈ ctx.active then
    match aggregateSignatureWithCtx S challenge ctx (st.commits.map (·.commitW)) st.shares with
    | some sig => some ⟨sig⟩
    | none => none
  else none

end IceNine.Protocol
