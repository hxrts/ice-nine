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
- `IceNine.Security`: Security proofs and threat models
-/

import IceNine.Crypto
import IceNine.Protocol.Core.Core
import IceNine.Protocol.DKG.Core
import IceNine.Protocol.DKG.Threshold
import IceNine.Protocol.Sign.Types
import IceNine.Protocol.Sign.Core
import IceNine.Protocol.Sign.Threshold
import IceNine.Protocol.Sign.Sign
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
import IceNine.Protocol.State.StateProduct
import IceNine.Protocol.State.ThresholdMerge
import IceNine.Protocol.DKG.VSSCore
import IceNine.Protocol.DKG.VSS
import IceNine.Protocol.Shares.RefreshCoord
import IceNine.Protocol.Shares.RepairCoord
import IceNine.Protocol.Core.Error
import IceNine.Norms
import IceNine.Instances
import IceNine.Samples
import IceNine.Security.Assumptions
import IceNine.Security.Correctness
import IceNine.Security.Lagrange
import IceNine.Security.Robustness
import IceNine.Security.DKG
import IceNine.Security.Sign
import IceNine.Security.Repair
import IceNine.Security.RefreshRepair
import IceNine.Security.Phase
import IceNine.Security.VSS
import IceNine.Security.Coordination
