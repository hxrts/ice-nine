/-
# Ice Nine - Cryptographic Protocol Verification

This is the main entry point for the Ice Nine formal verification library.

## Structure

- `IceNine.Crypto`: Cryptographic primitives and their properties
- `IceNine.Protocol.Core`: Core protocol types
- `IceNine.Protocol.DKGCore`: Distributed key generation (core + checks)
- `IceNine.Protocol.Sign`: Signing and verification (n-of-n, t-of-n)
- `IceNine.Security`: Security proofs and threat models
-/

import IceNine.Crypto
import IceNine.Protocol.Core
import IceNine.Protocol.DKGCore
import IceNine.Protocol.DKGThreshold
import IceNine.Protocol.Sign
import IceNine.Protocol.SignSession
import IceNine.Protocol.Dealer
import IceNine.Protocol.Refresh
import IceNine.Protocol.RefreshState
import IceNine.Protocol.Repair
import IceNine.Protocol.Rerandomize
import IceNine.Protocol.Phase
import IceNine.Protocol.PhaseIndexed
import IceNine.Protocol.PhaseHandlers
import IceNine.Protocol.PhaseSig
import IceNine.Protocol.PhaseMerge
import IceNine.Protocol.StateProduct
import IceNine.Protocol.ThresholdMerge
import IceNine.Protocol.Secret
import IceNine.Protocol.VSSCore
import IceNine.Protocol.VSS
import IceNine.Protocol.RefreshCoord
import IceNine.Protocol.RepairCoord
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
