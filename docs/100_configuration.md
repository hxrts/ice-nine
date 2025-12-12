## Local Rejection Signing

Ice Nine implements restart-free threshold Dilithium signing with local rejection sampling. Each signer applies rejection sampling locally before sending their partial signature, with bounds chosen so that any valid combination of partials automatically satisfies global bounds.

**Key invariant**: If each of T signers produces z_i with ‖z_i‖∞ ≤ B_local, then the aggregate z = Σz_i satisfies ‖z‖∞ ≤ T · B_local ≤ B_global.

This eliminates global rejection as a distributed control-flow path. Given sufficient honest parties (≥ threshold), signing **never** triggers a distributed restart due to rejection sampling.

### Configuration

```lean
-- Default: 2/3+1 threshold
let cfg := ThresholdConfig.mk' n globalBound

-- Custom threshold
let cfg := ThresholdConfig.mk' n globalBound (t := 5) (maxSigners := 5)
```
