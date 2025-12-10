# Ice Nine Protocol Specification

Ice Nine is a threshold signature scheme in the lattice setting. It follows the Schnorr pattern adapted for post-quantum security. The protocol operates in two rounds. Parties hold additive shares of a master secret. They produce partial signatures that aggregate into a single valid signature.

The design supports both $n$-of-$n$ and $t$-of-$n$ threshold configurations. In the $n$-of-$n$ case all parties must participate. In the $t$-of-$n$ case any subset of $t$ or more parties can sign. Lagrange interpolation coefficients adjust the partial shares in the threshold case.

## CRDT-Based State Management

The implementation uses a semilattice/CRDT architecture for protocol state. Each protocol phase (commit, reveal, shares, done) carries state that forms a join-semilattice. The join operation (⊔) merges states from different replicas or out-of-order message arrivals.

**Phase-indexed state.** Protocol progress is modeled as transitions between phases: commit → reveal → shares → done. Each phase carries accumulated data. States within a phase merge via componentwise join.

**Monotonic handlers.** Step functions that advance state are monotone with respect to the semilattice order. This ensures that merging divergent traces preserves safety properties. If $a \leq b$ then $\mathsf{step}(a) \leq \mathsf{step}(b)$.

**Composite state.** Protocol state combines with auxiliary CRDT data for refresh masks, repair bundles, and rerandomization masks. The product of semilattices is itself a semilattice.

## Linear Typing Discipline

The implementation uses wrapper types to enforce disciplined handling of secret material.

**SecretBox and NonceBox.** Secrets and nonces are wrapped in opaque structures that discourage pattern matching in public code. This signals intent and reduces accidental leakage, even without full linear types.

**Threshold context.** Signature extraction requires a `ThresholdCtx` that pairs the active signer set with a proof that $|S| \geq t$. This prevents signatures from being produced without sufficient participation.

## Specification Components

**Algebraic Setting.** Secrets live in a module $\mathcal{S}$ over a scalar ring. Public keys live in a module $\mathcal{P}$. A linear map $A : \mathcal{S} \to \mathcal{P}$ connects them. Commitments bind public values. A hash function produces challenges.

**Key Generation.** Two modes exist. A trusted dealer can sample the master secret and distribute shares. Alternatively parties can run a distributed key generation protocol. Both modes produce additive shares $s_i$ with $\sum_i s_i = s$. The DKG protocol uses the commit-reveal pattern with CRDT-mergeable state.

**Signing.** Signing proceeds in two rounds with phase-indexed state. In round one each party commits to a nonce. After all commits arrive parties reveal their nonces and compute a shared challenge. In round two each party produces a partial signature. An aggregator combines the partials into the final signature. State at each phase is mergeable.

**Verification.** A verifier checks the aggregated signature against the public key. The check uses the linear map $A$ and the hash function. The signature is valid if the recomputed challenge matches and the norm bound is satisfied.

**Extensions.** The protocol supports several extensions. Complaints identify misbehaving parties. Share refresh updates shares using zero-sum mask functions that merge via join. Share repair combines helper deltas via append-based bundles. Rerandomization applies zero-sum masks to shares and nonces with merge-preserving structure.

**Security.** The protocol assumes binding commitments and models the hash as a random oracle. Under these assumptions it achieves threshold unforgeability. Formal proofs reside in the Lean verification modules. Totality theorems ensure that validation functions always return either success or a structured error.

## Lattice Cryptography

The security of Ice Nine reduces to standard lattice hardness assumptions:

**Short Integer Solution (SIS).** Given matrix $A \in \mathbb{Z}_q^{n \times m}$, finding short $z$ with $Az = 0$ is hard. Signature unforgeability reduces to SIS: a forger that produces valid signatures can be used to solve SIS instances.

**Module Learning With Errors (MLWE).** Distinguishing $(A, As + e)$ from $(A, u)$ where $s, e$ are small is hard. Key secrecy reduces to MLWE: recovering the secret key from the public key requires solving MLWE.

**Rejection Sampling.** The signing protocol uses rejection sampling to ensure signatures are independent of the secret key. If the response norm exceeds the bound $\gamma_1 - \beta$, the party aborts and retries with a fresh nonce. Expected attempts: ~4 for Dilithium parameters.

**Parameter Validation.** The implementation includes lightweight parameter validation to catch obviously insecure configurations. Full security analysis requires the lattice estimator.

## Nonce Safety

**Critical property:** Nonce reuse completely breaks Schnorr-style signatures. If the same nonce $y$ is used with two different challenges $c_1, c_2$:
- $z_1 = y + c_1 \cdot sk$
- $z_2 = y + c_2 \cdot sk$
- Then $sk = (z_1 - z_2) / (c_1 - c_2)$

The protocol tracks used session IDs via `SessionTracker` to prevent this catastrophic failure mode.

## Docs Index

1. `01_algebra.md`: Algebraic primitives, module structure, lattice instantiations, and semilattice definitions
2. `02_keygen.md`: Dealer and distributed key generation with CRDT state, party exclusion
3. `03_signing.md`: Two-round signing protocol with phase-indexed state, rejection sampling
4. `04_verification.md`: Signature verification and threshold context
5. `05_extensions.md`: Complaints, refresh, repair, rerandomization with merge semantics
