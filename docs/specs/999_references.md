# References

Ice Nine adapts the FROST threshold signature pattern to the lattice setting. The protocol introduces local rejection sampling to eliminate distributed coordination for norm bounds. This section places Ice Nine in context with related work and identifies its novel contributions.

## Relationship to FROST

Ice Nine follows the FROST protocol structure closely. FROST is a two-round Schnorr threshold signature scheme that uses dual nonces and binding factors to prevent adaptive attacks. Ice Nine preserves these mechanisms while adapting them to Dilithium's algebraic structure.

The direct adaptations include the commit-reveal round structure, dual nonces for hiding and binding, per-signer binding factors, domain-separated hash functions, and proof of knowledge during DKG. The core insight transfers directly because Dilithium's response equation z = y + c·s has the same linear form as Schnorr.

## Novel Contributions

Ice Nine introduces several innovations beyond the FROST-to-lattice adaptation.

Local rejection sampling with triangle inequality guarantee is the primary innovation. Prior threshold Dilithium work faces exponential retry complexity as the number of participants increases. Ice Nine solves this by having each signer enforce a local bound. By setting the local bound to the global bound divided by the signer count, the triangle inequality guarantees the aggregate satisfies the global bound. No distributed retries are needed.

Ice Nine has a BFT-friendly design. The protocol validates each partial signature independently during aggregation. Invalid shares are discarded without affecting valid ones. With honest majority, sufficient valid partials always exist. Malicious parties cannot force distributed restarts.

CRDT-based protocol state enables conflict-free merging of divergent execution traces. Protocol state forms join-semilattices. This handles out-of-order messages and network partitions without additional coordination.

Compile-time nonce safety uses session types to make nonce reuse a compile-time error. Private constructors and consumption proofs enforce linear usage at the type level.

Formal verification in Lean 4 provides machine-checked proofs of correctness and security properties. Proofs include aggregation correctness, security reductions to SIS and MLWE, and CRDT safety via monotonicity of state transitions.

## Comparison with Related Work

| Scheme | Parties | Rejection Handling | BFT Design |
|--------|---------|-------------------|------------|
| DiLizium | 2 | Global retry | No |
| TOPCOAT | 2 | Cross-instance | No |
| PQShield compact | T ≤ 8 | Parallel instances | No |
| Ice Nine | Arbitrary t-of-n | Local bounds | Yes |

DiLizium and TOPCOAT are limited to two parties. The PQShield compact scheme supports small thresholds but runs T parallel Dilithium executions. Ice Nine supports arbitrary threshold configurations with local rejection sampling.

*Note: This comparison is based on a cursory literature search, there may be information missing from this review.*

## References

### FROST

- Komlo, Goldberg. FROST: Flexible Round-Optimized Schnorr Threshold Signatures. SAC 2020. [ePrint 2020/852](https://eprint.iacr.org/2020/852)

### Threshold Dilithium

- Vakarjuk et al. DiLizium: A Two-Party Lattice-Based Signature Scheme. Entropy 2021. [MDPI](https://www.mdpi.com/1099-4300/23/8/989)
- Snetkov, Vakarjuk, Laud. TOPCOAT: Towards Practical Two-Party CRYSTALS-Dilithium. 2024. [Springer](https://link.springer.com/article/10.1007/s10791-024-09449-2)
- Niot, del Pino. Finally! A Compact Lattice-Based Threshold Signature. PKC 2025. [PQShield](https://pqshield.com/publications/finally-a-compact-lattice-based-threshold-signature/)

### Lattice Cryptography

- Lyubashevsky. Fiat-Shamir with Aborts. ASIACRYPT 2009.
- Ducas et al. CRYSTALS-Dilithium. NIST PQC Round 3.
- NIST FIPS 204. ML-DSA (Dilithium) Standard. 2024. [NIST](https://csrc.nist.gov/pubs/fips/204/final)

### Byzantine Fault Tolerance

- Cachin et al. Byzantine Fault-Tolerant Aggregate Signatures. ASIACCS 2024. [ACM](https://dl.acm.org/doi/10.1145/3634737.3657020)

### Surveys

- Cozzo, Smart. Sharing the LUOV: Threshold Post-Quantum Signatures. NIST PQC 2019. [NIST](https://csrc.nist.gov/CSRC/media/Events/Second-PQC-Standardization-Conference/documents/accepted-papers/cozzo-luov-paper.pdf)
- University of Bern. Implementation of a Threshold Post-Quantum Signature. Thesis 2022. [Bern](https://crypto.unibe.ch/theses/2022-post-quandum-threshold-signature/)
