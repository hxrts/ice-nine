# Ice Nine

A threshold signature scheme using lattice cryptography. As [Matthew Green has noted](https://blog.cryptographyengineering.com/2023/11/30/to-schnorr-and-beyond-part-2/), Dilithium follows the Schnorr pattern adapted to lattice assumptions for post-quantum security. This protocol extends that structure to the threshold setting where multiple parties hold secret shares and collaborate to sign messages without reconstructing the full key.

The implementation is written in Lean with proofs of correctness. Security reduces to the Short Integer Solution and Module Learning With Errors problems. The protocol supports distributed key generation, proactive refresh, and share repair.

The design and implementation draws heavily from [FROST](https://eprint.iacr.org/2020/852), [developed](https://github.com/ZcashFoundation/frost) by the Zcash Foundation.

"Ice Nine" is a nod to [Cat's Cradle](https://en.wikipedia.org/wiki/Ice-nine) and [Dilithium](https://pq-crystals.org/dilithium/).

## Quick start
```bash
nix develop
lake check
```

## License

[Apache-2.0](LICENSE)
