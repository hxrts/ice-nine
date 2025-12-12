/-
# Ice Nine - Cryptographic Protocol Verification

This is the main entry point for the Ice Nine formal verification library.

## Structure

- `IceNine.Crypto`: Cryptographic primitives and their properties
- `IceNine.Protocol.Core`: Core types, security markers, patterns, error handling
- `IceNine.Protocol.Sign`: Signing protocol (types, core, threshold, sessions)
- `IceNine.Protocol.DKG`: Distributed key generation, VSS, dealer mode
- `IceNine.Protocol.Shares`: Share management (refresh, repair, rerandomize)
- `IceNine.Protocol.State`: Phase state, CRDT merging, threshold-aware operations
- `IceNine.Proofs`: Formal proofs (correctness, soundness, extensions)
-/

import IceNine.Crypto
import IceNine.Protocol.Core.Core
import IceNine.Protocol.Core.CRDT
import IceNine.Protocol.DKG.Core
import IceNine.Protocol.DKG.Threshold
import IceNine.Protocol.Sign.Types
import IceNine.Protocol.Sign.Core
import IceNine.Protocol.Sign.Threshold
import IceNine.Protocol.Sign.Session
import IceNine.Protocol.Core.Serialize
import IceNine.Protocol.DKG.Dealer
import IceNine.Protocol.Shares.Refresh
import IceNine.Protocol.Shares.RefreshState
import IceNine.Protocol.Shares.Repair
import IceNine.Protocol.Shares.Rerandomize
import IceNine.Protocol.State.Phase
import IceNine.Protocol.State.PhaseIndexed
import IceNine.Protocol.State.PhaseHandlers
import IceNine.Protocol.State.PhaseSig
import IceNine.Protocol.State.PhaseMerge
import IceNine.Protocol.Sign.ThresholdMerge
import IceNine.Protocol.DKG.Feldman
import IceNine.Protocol.DKG.VSSDKG
import IceNine.Protocol.Shares.RefreshCoord
import IceNine.Protocol.Shares.RepairCoord
import IceNine.Protocol.Core.Error
import IceNine.Norms
import IceNine.Instances
import IceNine.Samples
-- Proofs/Core
import IceNine.Proofs.Core.Assumptions
import IceNine.Proofs.Core.ListLemmas
import IceNine.Proofs.Core.HighBits
-- Proofs/Correctness
import IceNine.Proofs.Correctness.Correctness
import IceNine.Proofs.Correctness.Lagrange
import IceNine.Proofs.Correctness.DKG
import IceNine.Proofs.Correctness.Sign
-- Proofs/Soundness
import IceNine.Proofs.Soundness.Soundness
import IceNine.Proofs.Soundness.Robustness
import IceNine.Proofs.Soundness.VSS
-- Proofs/Extensions
import IceNine.Proofs.Extensions.Phase
import IceNine.Proofs.Extensions.Coordination
import IceNine.Proofs.Extensions.Repair
import IceNine.Proofs.Extensions.RefreshRepair
