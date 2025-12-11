# Ice Nine Protocol Specification

Ice Nine is a threshold signature scheme in the lattice setting. It follows the Schnorr pattern adapted for post-quantum security. The protocol operates in two rounds. Parties hold additive shares of a master secret. They produce partial signatures that aggregate into a single valid signature.

The design supports both $n$-of-$n$ and $t$-of-$n$ threshold configurations. In the $n$-of-$n$ case all parties must participate. In the $t$-of-$n$ case any subset of $t$ or more parties can sign. Lagrange interpolation coefficients adjust the partial shares in the threshold case.

## CRDT-Based State Management

The implementation uses a semilattice/CRDT architecture for protocol state. Each protocol phase (commit, reveal, shares, done) carries state that forms a join-semilattice. The join operation (⊔) merges states from different replicas or out-of-order message arrivals.

**Phase-indexed state.** Protocol progress is modeled as transitions between phases: commit → reveal → shares → done. Each phase carries accumulated data. States within a phase merge via componentwise join. The type-indexed implementation (`Protocol/PhaseIndexed.lean`) makes invalid phase transitions compile-time errors.

**Conflict-free message maps.** Messages are stored in `MsgMap` structures keyed by sender ID. This makes conflicting messages from the same sender un-expressable in the type system. Each party can contribute at most one message per phase. The `tryInsert` operation returns a conflict indicator for strict validation, while `insert` silently ignores duplicates for CRDT merge semantics.

**Monotonic handlers.** Step functions that advance state are monotone with respect to the semilattice order. This ensures that merging divergent traces preserves safety properties. If $a \leq b$ then $\mathsf{step}(a) \leq \mathsf{step}(b)$.

**Composite state.** Protocol state combines with auxiliary CRDT data for refresh masks, repair bundles, and rerandomization masks. The product of semilattices is itself a semilattice.

## Session Types

The implementation uses session types to enforce disciplined handling of secret material, making certain classes of errors impossible to express.

**Session-typed signing.** The signing protocol (`Protocol/SignSession.lean`) uses linear session types where each state transition consumes the previous state. Nonces are wrapped in `FreshNonce` structures that can only be consumed once—nonce reuse is a compile-time error, not a runtime check.

**Threshold context.** Signature extraction requires a `ThresholdCtx` that pairs the active signer set with a proof that $|S| \geq t$. This prevents signatures from being produced without sufficient participation.

## Specification Components

**Algebraic Setting.** Secrets live in a module $\mathcal{S}$ over a scalar ring. Public keys live in a module $\mathcal{P}$. A linear map $A : \mathcal{S} \to \mathcal{P}$ connects them. Commitments bind public values. A hash function produces challenges.

**Key Generation.** Two modes exist. A trusted dealer can sample the master secret and distribute shares. Alternatively parties can run a distributed key generation protocol. Both modes produce additive shares $s_i$ with $\sum_i s_i = s$. The DKG protocol uses the commit-reveal pattern with CRDT-mergeable state. Following FROST, each party provides a proof of knowledge (PoK) during DKG to prevent rogue-key attacks. For malicious security, Verifiable Secret Sharing (VSS) allows parties to verify shares against polynomial commitments.

**Signing.** Signing proceeds in two rounds with phase-indexed state. In round one each party commits to a nonce. After all commits arrive parties reveal their nonces and compute a shared challenge. In round two each party produces a partial signature. An aggregator combines the partials into the final signature. State at each phase is mergeable.

**Verification.** A verifier checks the aggregated signature against the public key. The check uses the linear map $A$ and the hash function. The signature is valid if the recomputed challenge matches and the norm bound is satisfied.

**Extensions.** The protocol supports several extensions. Complaints identify misbehaving parties. Share refresh updates shares using zero-sum mask functions that merge via join; two refresh modes are available: a coordinator-based protocol (`Protocol/RefreshCoord.lean`) and a fully distributed DKG-based protocol (`Protocol/RefreshDKG.lean`) where parties contribute zero-polynomials without a trusted coordinator. Share repair combines helper deltas via append-based bundles; a coordination protocol (`Protocol/RepairCoord.lean`) handles Lagrange coefficient computation and contribution verification. Rerandomization applies zero-sum masks to shares and nonces with merge-preserving structure.

**Security.** The protocol assumes binding commitments and models the hash as a random oracle. Under these assumptions it achieves threshold unforgeability. Formal proofs reside in the Lean verification modules. Totality theorems ensure that validation functions always return either success or a structured error.

## Module Organization

The implementation is organized into focused modules:

**Protocol Core:**
- `Protocol/Core.lean` - Scheme record, key shares, DKG messages, security documentation
- `Protocol/SignTypes.lean` - Session tracking, signing messages, error types
- `Protocol/SignCore.lean` - Challenge computation, n-of-n aggregation
- `Protocol/SignThreshold.lean` - Coefficient strategies, threshold context
- `Protocol/Sign.lean` - Re-exports from split modules for backward compatibility
- `Protocol/SignSession.lean` - Session-typed API preventing nonce reuse

**VSS and DKG:**
- `Protocol/VSSCore.lean` - Polynomial commitments, share verification
- `Protocol/VSS.lean` - VSS transcript, complaint mechanism
- `Protocol/DKGCore.lean` - Basic DKG protocol
- `Protocol/DKGThreshold.lean` - Threshold DKG with exclusion

**Share Management:**
- `Protocol/Refresh.lean` - Share refresh with zero-sum masks
- `Protocol/RefreshCoord.lean` - Coordinator-based refresh protocol
- `Protocol/RefreshDKG.lean` - DKG-based distributed refresh (no coordinator)
- `Protocol/Repair.lean` - Share repair protocol
- `Protocol/RepairCoord.lean` - Repair coordination with commit-reveal
- `Protocol/Rerandomize.lean` - Signature rerandomization

**Infrastructure:**
- `Protocol/Phase.lean` - Phase state with MsgMap CRDT
- `Protocol/PhaseIndexed.lean` - Type-indexed phase transitions
- `Protocol/Lagrange.lean` - Unified Lagrange coefficient API
- `Protocol/Error.lean` - BlameableError typeclass, error utilities
- `Protocol/Serialize.lean` - Serialization API for network transport

**Security:**
- `Security/Assumptions.lean` - Cryptographic assumptions, axiom index
- `Security/Correctness.lean` - Verification theorems
- `Security/VSS.lean` - VSS security properties

## Lattice Cryptography

The security of Ice Nine reduces to standard lattice hardness assumptions:

**Short Integer Solution (SIS).** Given matrix $A \in \mathbb{Z}_q^{n \times m}$, finding short $z$ with $Az = 0$ is hard. Signature unforgeability reduces to SIS: a forger that produces valid signatures can be used to solve SIS instances.

**Module Learning With Errors (MLWE).** Distinguishing $(A, As + e)$ from $(A, u)$ where $s, e$ are small is hard. Key secrecy reduces to MLWE: recovering the secret key from the public key requires solving MLWE.

**Rejection Sampling.** The signing protocol uses rejection sampling to ensure signatures are independent of the secret key. If the response norm exceeds the bound $\gamma_1 - \beta$, the party aborts and retries with a fresh nonce. Expected attempts: ~4 for Dilithium parameters.

**Parameter Validation.** The implementation includes lightweight parameter validation to catch obviously insecure configurations. The standard parameter sets follow [NIST FIPS 204 (ML-DSA/Dilithium)](https://csrc.nist.gov/pubs/fips/204/final).

## Nonce Safety

**Critical property:** Nonce reuse completely breaks Schnorr-style signatures. If the same nonce $y$ is used with two different challenges $c_1, c_2$:
- $z_1 = y + c_1 \cdot sk$
- $z_2 = y + c_2 \cdot sk$
- Then $sk = (z_1 - z_2) / (c_1 - c_2)$

The session-typed signing protocol makes nonce reuse a compile-time error. Each `FreshNonce` can only be consumed once, and the type system enforces that signing sessions progress linearly through states without backtracking.

## Implementation Security

The implementation includes comprehensive security documentation in `Protocol/Core.lean`:

**Randomness Requirements:** All secret values (shares, nonces, commitment openings) must be sampled from a CSPRNG. Nonce reuse is catastrophic—the session-typed API makes it a compile-time error.

**Side-Channel Considerations:** The specification flags timing-vulnerable functions (Lagrange computation, norm checks). Production implementations must use constant-time primitives. The `ConstantTimeEq` typeclass marks types requiring constant-time equality comparison.

**Memory Zeroization:** Sensitive values must be securely erased after use. Platform-specific APIs are documented for C, POSIX, Windows, and Rust. The `Zeroizable` typeclass marks types requiring secure erasure.

**Secret Wrappers:** The `SecretBox` type wraps secret shares with a private constructor, discouraging accidental duplication or exposure.

## Docs Index

1. [Algebraic Setting](01_algebra.md): Algebraic primitives, module structure, lattice instantiations, and semilattice definitions
2. [Key Generation](02_keygen.md): Dealer and distributed key generation with CRDT state, VSS, party exclusion
3. [Signing Protocol](03_signing.md): Two-round signing protocol with session types, rejection sampling
4. [Verification](04_verification.md): Signature verification and threshold context
5. [Extensions](05_extensions.md): Complaints, refresh/repair coordination, rerandomization, type-indexed phases
