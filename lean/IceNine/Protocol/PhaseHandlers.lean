/-
# Phase-indexed handlers

Handlers consume a state at a given phase and produce a state at the next phase,
while being monotone with respect to the semilattice merge. This allows CRDT
merging of divergent traces without breaking safety properties. Threshold
context is handled separately when aggregating signatures.
-/

import IceNine.Protocol.Phase
import IceNine.Protocol.DKGCore
import IceNine.Protocol.DKGThreshold
import IceNine.Protocol.Sign
import IceNine.Protocol.ThresholdMerge

namespace IceNine.Protocol

open List

-- Step within commit phase: add a commit message (monotone append).
def stepCommit
  (S : Scheme)
  (msg : DkgCommitMsg S)
  (st  : CommitState S) : CommitState S :=
{ commits := st.commits ⊔ [msg] }

-- Step within reveal phase: add a reveal message (monotone append).
def stepReveal
  (S : Scheme)
  (msg : DkgRevealMsg S)
  (st  : RevealState S) : RevealState S :=
{ commits := st.commits, reveals := st.reveals ⊔ [msg] }

-- Step within shares phase: add a signature share (monotone append).
def stepShare
  (S : Scheme)
  (msg : SignShareMsg S)
  (st  : ShareWithCtx S) : ShareWithCtx S :=
let st' : ShareState S := { commits := st.state.commits,
                            reveals := st.state.reveals,
                            shares  := st.state.shares ⊔ [msg],
                            active  := st.state.active }
⟨st', st.ctx⟩

-- Attempt to finalize into a Signature when the active set meets threshold.
def tryAggregate
  (S : Scheme)
  (swc : ShareWithCtx S)
  (challenge : S.Challenge)
  (coeffs : List (LagrangeCoeff S))
  : Option (DoneState S) :=
  let ctx := swc.ctx
  let st  := swc.state
  if hfrom : ∀ sh ∈ st.shares, sh.from ∈ ctx.active then
    some { sig := aggregateSignatureLagrangeThresh S challenge ctx (st.commits.map (·.commitW)) coeffs st.shares }
  else
    none

end IceNine.Protocol
