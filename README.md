# Ice Nine

Schnorr-inspired Lattice-based threshold signatures with Lean proofs.

- Lean models: core scheme, DKG (core + t-of-n with complaints), two-round signing (n-of-n, t-of-n), dealer keygen, refresh, repair, rerandomized signing, phase/CRDT state.
- Security: correctness/robustness lemmas and assumption scaffolding (binding commits, RO hash, norm bounds).
- Instances/Norms/Samples: demo schemes (Int, ZMod, vectors), norm predicates, `#eval` transcripts.

## Quick start
```bash
nix develop
lake check
```

## License

[Apache-2.0](LICENSE)
