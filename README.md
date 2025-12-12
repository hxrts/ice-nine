# Ice Nine

A threshold signature scheme using lattice cryptography. As [Matthew Green has noted](https://blog.cryptographyengineering.com/2023/11/30/to-schnorr-and-beyond-part-2/), Dilithium follows the Schnorr pattern adapted to lattice assumptions for post-quantum security. This protocol extends that structure to the threshold setting where multiple parties hold secret shares and collaborate to sign messages without reconstructing the full key.

The implementation is written in Lean with proofs of correctness. Security reduces to the Short Integer Solution and Module Learning With Errors problems. The protocol supports distributed key generation, proactive refresh, and share repair.

The design and implementation draws heavily from [FROST](https://eprint.iacr.org/2020/852), [developed](https://github.com/ZcashFoundation/frost) by the Zcash Foundation.

"Ice Nine" is a nod to [Cat's Cradle](https://en.wikipedia.org/wiki/Ice-nine) and [Dilithium](https://pq-crystals.org/dilithium/).

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

## Quick start
```bash
nix develop
lake check
```

## License

[Apache-2.0](LICENSE)
