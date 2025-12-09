# Ice Nine Protocol Specification

Ice Nine is a threshold signature scheme in the lattice setting. It follows the Schnorr pattern adapted for post-quantum security. The protocol operates in two rounds. Parties hold additive shares of a master secret. They produce partial signatures that aggregate into a single valid signature.

The design supports both $n$-of-$n$ and $t$-of-$n$ threshold configurations. In the $n$-of-$n$ case all parties must participate. In the $t$-of-$n$ case any subset of $t$ or more parties can sign. Lagrange interpolation coefficients adjust the partial shares in the threshold case.

This specification covers the following components.

**Algebraic Setting.** Secrets live in a module $\mathcal{S}$ over a scalar ring. Public keys live in a module $\mathcal{P}$. A linear map $A : \mathcal{S} \to \mathcal{P}$ connects them. Commitments bind public values. A hash function produces challenges.

**Key Generation.** Two modes exist. A trusted dealer can sample the master secret and distribute shares. Alternatively parties can run a distributed key generation protocol. Both modes produce additive shares $s_i$ with $\sum_i s_i = s$.

**Signing.** Signing proceeds in two rounds. In round one each party commits to a nonce. After all commits arrive parties reveal their nonces and compute a shared challenge. In round two each party produces a partial signature. An aggregator combines the partials into the final signature.

**Verification.** A verifier checks the aggregated signature against the public key. The check uses the linear map $A$ and the hash function. The signature is valid if the recomputed challenge matches.

**Extensions.** The protocol supports several extensions. Complaints identify misbehaving parties. Share refresh updates shares without changing the public key. Share repair lets a party recover a lost share from helpers. Rerandomization adds masks to shares and nonces for unlinkability.

**Security.** The protocol assumes binding commitments and models the hash as a random oracle. Under these assumptions it achieves threshold unforgeability. Formal proofs reside in the Lean verification modules.

## Document Structure

- `01_algebra.md`: Algebraic primitives and module structure
- `02_keygen.md`: Dealer and distributed key generation
- `03_signing.md`: Two-round signing protocol
- `04_verification.md`: Signature verification
- `05_extensions.md`: Complaints, refresh, repair, rerandomization
- `06_assumptions.md`: Security model and assumptions
