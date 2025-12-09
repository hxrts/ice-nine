# Ice Nine

Lattice-based threshold signature scheme with signing + DKG.

Lean models for core scheme, DKG (core + t-of-n with complaints), two-round signing (n-of-n, t-of-n), dealer keygen, refresh, repair, and rerandomized signing.

Security proofs for correctness/robustness lemmas and assumption scaffolding (binding commits, RO hash, norm bounds).

## Quick start
```bash
nix develop      # or use your Lean toolchain
lake check       # when lake is available
```

License: Apache-2.0
