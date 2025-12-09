# Ice Nine

Lattice-based threshold signature scheme with DKG, and signing.

## What’s here
- **Lean models**: core scheme, DKG (core + t-of-n with complaints), two-round signing (n-of-n, t-of-n), dealer keygen, refresh, repair, rerandomized signing.
- **Security**: correctness/robustness lemmas and assumption scaffolding (binding commits, RO hash, norm bounds).
- **Instances/Norms/Samples**: demo schemes (Int, ZMod, vectors), norm predicates, `#eval` transcripts.

## Quick start (Lean)
```bash
nix develop      # or use your Lean toolchain
lake check       # when lake is available
```

License: Apache-2.0
