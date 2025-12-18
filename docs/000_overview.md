# Ice Nine Protocol Specification Overview

Ice Nine is a threshold signature scheme in the lattice setting. It follows the Schnorr pattern adapted for post-quantum security. The protocol operates in two rounds. Parties hold additive shares of a master secret. They produce partial signatures that aggregate into a single valid signature.

The design supports both $n$-of-$n$ and $t$-of-$n$ threshold configurations. In the $n$-of-$n$ case all parties must participate. In the $t$-of-$n$ case any subset of $t$ or more parties can sign. Lagrange interpolation coefficients adjust the partial shares in the threshold case.

## Getting Started

This section provides a practical overview of the protocol flow from key generation through signing.

### Protocol Flow

A typical deployment follows these steps.

1. **Configuration**: Create a `ThresholdConfig` with party count, threshold, and security parameters.
2. **Key Generation**: Run DKG to establish shared key material. Each party receives a secret share.
3. **Signing Sessions**: For each message, run the two-round signing protocol to produce a threshold signature.
4. **Verification**: Any party can verify signatures using the public key.

### Configuration

Start by creating a threshold configuration.

```lean
-- Create configuration for 5 parties with Dilithium2 security
let cfg := ThresholdConfig.dilithium2 5

-- The default threshold is 2/3+1 = 4 for 5 parties
-- cfg.threshold = 4
-- cfg.globalBound = 130994
-- cfg.localBound = 32748
```

See [Local Rejection Signing](100_configuration.md) for detailed parameter guidance.

### Key Generation

Run distributed key generation to establish shared keys.

```lean
-- Each party generates their DKG contribution
let (commitMsg, secretState) := dkgCommit S partyId randomness

-- Broadcast commit messages, then reveal
let revealMsg := dkgReveal S secretState

-- After receiving all reveals, compute key shares
let keyShare := dkgFinalize S partyId allCommits allReveals
```

The DKG protocol uses commit-reveal to prevent rogue-key attacks. Each party receives a `KeyShare` containing their secret share and the global public key. See [Key Generation](002_keygen.md) for DKG modes and VSS.

### Signing

Signing proceeds in two rounds with session types enforcing correct usage.

```lean
-- Round 1: Commit to nonces
let nonce := FreshNonce.sample S  -- Sample fresh nonce
let ready := initSession S keyShare message session nonce
let (committed, commitMsg) := commit S ready
-- Broadcast commitMsg

-- After receiving all commits, reveal
let (revealed, revealMsg) := reveal S committed challenge bindingFactor aggregateW
-- Broadcast revealMsg

-- Round 2: Produce signature share
let (signed, shareMsg) ← signWithLocalRejection S revealed cfg sampleNonce
-- Broadcast shareMsg

-- Aggregator combines shares
let signature := aggregateValidated S cfg protocolCfg challenge commits shares pkShares factors
```

The `FreshNonce` type ensures nonces are used exactly once. The `signWithLocalRejection` function handles norm bounds locally without distributed retries. See [Two-Round Threshold Signing](003_signing.md) for the complete protocol.

### Verification

Verify signatures against the public key.

```lean
let valid := verify S signature publicKey message
```

Verification checks the algebraic relation A(z) = w + c·pk and the norm bound. See [Verification](004_verification.md) for details.

### Error Handling

Protocol operations return structured errors for recovery.

```lean
match result with
| .ok signature => -- Success
| .error e =>
    -- Check if error identifies a misbehaving party
    match BlameableError.blamedParty e with
    | some party => excludeParty party
    | none => handleOperationalError e
```

See [Extensions](005_extensions.md) for error recovery patterns across protocol phases.

### Extension Operations

After initial setup, use extension protocols for operational needs.

**Share Refresh** updates shares without changing the key. Run periodically for proactive security.

**Share Repair** recovers a lost share using contributions from other parties.

**Rerandomization** masks shares and nonces for unlinkability between sessions.

See [Extensions](005_extensions.md) for these protocols.

## CRDT-Based State Management

The implementation uses a semilattice/CRDT architecture for protocol state. Each protocol phase (commit, reveal, shares, done) carries state that forms a join-semilattice. The join operation (⊔) merges states from different replicas or out-of-order message arrivals.

Protocol progress is modeled as transitions between phases: commit → reveal → shares → done. Each phase carries accumulated data. States within a phase merge via componentwise join. The type-indexed implementation (`Protocol/State/PhaseIndexed.lean`) makes invalid phase transitions compile-time errors.

Messages are stored in `MsgMap` structures keyed by sender ID. This makes conflicting messages from the same sender un-expressable in the type system. Each party can contribute at most one message per phase.

The coordination protocols (RefreshCoord, RepairCoord) cleanly separate concerns into three layers:
- CRDT layer (`process*`): Pure merge semantics that are idempotent, commutative, and always succeed. Use for replication and networking.
- Validation layer (`detect*`, `validate*`): Conflict detection without modifying state. Use for auditing and security.
- Combined (`process*Validated`): Merge and validation in one call, returning `(newState, Option error)`.

Step functions that advance state are monotone with respect to the semilattice order. This ensures that merging divergent traces preserves safety properties. If $a \leq b$ then $\mathsf{step}(a) \leq \mathsf{step}(b)$.

Protocol state combines with auxiliary CRDT data for refresh masks, repair bundles, and rerandomization masks. The product of semilattices is itself a semilattice.

## Session Types

The implementation uses session types to enforce disciplined handling of secret material, making certain classes of errors impossible to express.

The signing protocol (`Protocol/Sign/Session.lean`) uses linear session types where each state transition consumes the previous state. Nonces are wrapped in `FreshNonce` structures that can only be consumed once. Nonce reuse is a compile-time error, not a runtime check.

Signature extraction requires a `ThresholdCtx` that pairs the active signer set with a proof that $|S| \geq t$. This prevents signatures from being produced without sufficient participation.

## Specification Components

**Algebraic Setting.** Secrets live in a module $\mathcal{S}$ over a scalar ring. Public keys live in a module $\mathcal{P}$. A linear map $A : \mathcal{S} \to \mathcal{P}$ connects them. Commitments bind public values. A hash function produces challenges.

**Key Generation.** Two modes exist. A trusted dealer can sample the master secret and distribute shares. Alternatively parties can run a distributed key generation protocol. Both modes produce additive shares $s_i$ with $\sum_i s_i = s$. The DKG protocol uses the commit-reveal pattern with CRDT-mergeable state. Following FROST, each party provides a proof of knowledge (PoK) during DKG to prevent rogue-key attacks. For malicious security, Verifiable Secret Sharing (VSS) allows parties to verify shares against polynomial commitments.

**Signing.** Signing proceeds in two rounds with phase-indexed state. In round one each party commits to a nonce. After all commits arrive parties reveal their nonces and compute a shared challenge. In round two each party produces a partial signature. An aggregator combines the partials into the final signature. State at each phase is mergeable.

**Verification.** A verifier checks the aggregated signature against the public key. The check uses the linear map $A$ and the hash function. The signature is valid if the recomputed challenge matches and the norm bound is satisfied.

**Extensions.** The protocol supports several extensions. Complaints identify misbehaving parties. Share refresh updates shares using zero-sum mask functions that merge via join; two refresh modes are available: a coordinator-based protocol (`Protocol/Shares/RefreshCoord.lean`) and a fully distributed DKG-based protocol (`Protocol/Shares/RefreshDKG.lean`) where parties contribute zero-polynomials without a trusted coordinator. Share repair combines helper deltas via append-based bundles; a coordination protocol (`Protocol/Shares/RepairCoord.lean`) handles Lagrange coefficient computation and contribution verification. Rerandomization applies zero-sum masks to shares and nonces with merge-preserving structure.

**Security.** The protocol assumes binding commitments and models the hash as a random oracle. Under these assumptions it achieves threshold unforgeability. Formal proofs reside in the Lean verification modules. Totality theorems ensure that validation functions always return either success or a structured error.

## Module Organization

The implementation is organized into focused modules within subdirectories:

**Protocol/Core/** - Foundation types and utilities:
- `Core/Core.lean` - Scheme record, key shares, DKG messages, linear security wrappers
- `Core/CRDT.lean` - CRDT primitives: Join typeclass, MsgMap sender-keyed collection
- `Core/Security.lean` - Security markers (Zeroizable, ConstantTimeEq), SecretBox, NonceBox
- `Core/Patterns.lean` - Reusable patterns: constraint aliases, commit-reveal framework, utilities
- `Core/Error.lean` - BlameableError typeclass, error utilities
- `Core/Lagrange.lean` - Unified Lagrange coefficient API
- `Core/Serialize.lean` - Serialization API for network transport
- `Core/ThresholdConfig.lean` - Threshold configuration and local rejection bounds
- `Core/NormBounded.lean` - Norm bound predicates and verification
- `Core/Abort.lean` - Session-level abort coordination for liveness failures

**Protocol/Sign/** - Signing protocol:
- `Sign/Types.lean` - Session tracking, signing messages, error types
- `Sign/Core.lean` - Challenge computation, n-of-n aggregation
- `Sign/Threshold.lean` - Coefficient strategies, threshold context
- `Sign/Session.lean` - Session-typed API preventing nonce reuse
- `Sign/ThresholdMerge.lean` - Threshold-aware state merge operations
- `Sign/LocalRejection.lean` - Local rejection sampling for norm bounds
- `Sign/ValidatedAggregation.lean` - Validated signature aggregation
- `Sign/NonceLifecycle.lean` - Nonce lifecycle tracking and safety
- `Sign/Sign.lean` - Re-exports for backward compatibility

**Protocol/DKG/** - Distributed key generation:
- `DKG/Core.lean` - Basic DKG protocol
- `DKG/Threshold.lean` - Threshold DKG with exclusion
- `DKG/Feldman.lean` - Polynomial commitments, share verification
- `DKG/VSSDKG.lean` - VSS transcript, complaint mechanism
- `DKG/Dealer.lean` - Trusted dealer mode

**Protocol/Shares/** - Share management:
- `Shares/Refresh.lean` - Share refresh with zero-sum masks
- `Shares/RefreshCoord.lean` - Coordinator-based refresh protocol
- `Shares/RefreshDKG.lean` - DKG-based distributed refresh (no coordinator)
- `Shares/RefreshState.lean` - Refresh state CRDT
- `Shares/Repair.lean` - Share repair protocol
- `Shares/RepairCoord.lean` - Repair coordination with commit-reveal
- `Shares/Rerandomize.lean` - Signature rerandomization

**Protocol/State/** - Phase state and CRDT operations:
- `State/Phase.lean` - Phase state with MsgMap CRDT
- `State/PhaseIndexed.lean` - Type-indexed phase transitions
- `State/PhaseHandlers.lean` - Phase transition handlers
- `State/PhaseSig.lean` - Phase signatures
- `State/PhaseMerge.lean` - Composite state merging

**Top-level modules:**
- `Crypto.lean` - Cryptographic primitives (hash, commitment)
- `Instances.lean` - Concrete scheme instantiations (Int, ZMod)
- `Norms.lean` - Norm bounds for lattice parameters
- `Samples.lean` - Sample transcript generation for testing

**Proofs/** - Formal verification (separate from protocol):

*Proofs/Core/* - Foundation for proofs:
- `Proofs/Core/Assumptions.lean` - Cryptographic assumptions, axiom index, Dilithium parameters
- `Proofs/Core/ListLemmas.lean` - Reusable lemmas for list operations and sums
- `Proofs/Core/HighBits.lean` - HighBits specification for Dilithium error absorption
- `Proofs/Core/NormProperties.lean` - Norm bound properties and lemmas
- `Proofs/Core/MsgMapLemmas.lean` - MsgMap CRDT lemmas

*Proofs/Correctness/* - Happy-path proofs:
- `Proofs/Correctness/Correctness.lean` - Verification theorems
- `Proofs/Correctness/DKG.lean` - DKG correctness proofs
- `Proofs/Correctness/Sign.lean` - Signing correctness proofs
- `Proofs/Correctness/Lagrange.lean` - Lagrange interpolation correctness
- `Proofs/Correctness/ThresholdConfig.lean` - Threshold configuration correctness

*Proofs/Soundness/* - Security proofs:
- `Proofs/Soundness/Soundness.lean` - Special soundness, nonce reuse attack, SIS reduction
- `Proofs/Soundness/VSS.lean` - VSS security properties
- `Proofs/Soundness/Robustness.lean` - Protocol robustness properties
- `Proofs/Soundness/LocalRejection.lean` - Local rejection sampling soundness

*Proofs/Extensions/* - Extension protocol proofs:
- `Proofs/Extensions/Phase.lean` - Phase handler monotonicity (CRDT safety)
- `Proofs/Extensions/Coordination.lean` - Refresh/repair coordination security
- `Proofs/Extensions/RefreshCoord.lean` - Refresh coordination proofs
- `Proofs/Extensions/Repair.lean` - Share repair correctness
- `Proofs/Extensions/RefreshRepair.lean` - Refresh invariants, rerandomization

## Lattice Cryptography

The security of Ice Nine reduces to standard lattice hardness assumptions:

**Short Integer Solution (SIS).** Given matrix $A \in \mathbb{Z}_q^{n \times m}$, finding short $z$ with $Az = 0$ is hard. Signature unforgeability reduces to SIS: a forger that produces valid signatures can be used to solve SIS instances.

**Module Learning With Errors (MLWE).** Distinguishing $(A, As + e)$ from $(A, u)$ where $s, e$ are small is hard. Key secrecy reduces to MLWE: recovering the secret key from the public key requires solving MLWE.

**Rejection Sampling.** The signing protocol uses rejection sampling to ensure signatures are independent of the secret key. If the response norm exceeds the bound $\gamma_1 - \beta$, the party aborts and retries with a fresh nonce. Expected attempts: ~4 for Dilithium parameters.

**Parameter Validation.** The implementation includes lightweight parameter validation to catch obviously insecure configurations. The standard parameter sets follow [NIST FIPS 204 (ML-DSA/Dilithium)](https://csrc.nist.gov/pubs/fips/204/final).

## Linear Types for Security-Critical Values

The implementation uses linear-style type discipline to prevent misuse of single-use values. While Lean doesn't have true linear types, private constructors and module-scoped access functions make violations visible and intentional.

**Linear wrappers:**

| Type | Purpose | Consequence of Misuse |
|------|---------|----------------------|
| `FreshNonce` | Signing nonces | Nonce reuse → key recovery |
| `LinearMask` | Refresh masks | Double-apply → zero-sum violation |
| `LinearDelta` | Repair deltas | Double-use → corrupted share |
| `LinearOpening` | Commitment randomness | Reuse → equivocation possible |

**Pattern:** Each wrapper has:
1. Private constructor (`private mk`) - prevents arbitrary creation
2. Private value field - prevents direct access outside module
3. Public creation function - controlled entry point
4. `consume` function - extracts value and produces consumption proof

```lean
structure LinearMask (S : Scheme) where
  private mk ::
  private partyId : S.PartyId
  private maskValue : S.Secret
  private publicImage : S.Public

def LinearMask.consume (m : LinearMask S) : S.Secret × MaskConsumed S
```

The consumption proof (`MaskConsumed`, `DeltaConsumed`, `OpeningConsumed`) can be required by downstream functions to ensure the value was properly consumed.

## Nonce Safety

**Critical property:** Nonce reuse completely breaks Schnorr-style signatures. If the same nonce $y$ is used with two different challenges $c_1, c_2$:
- $z_1 = y + c_1 \cdot sk$
- $z_2 = y + c_2 \cdot sk$
- Then $sk = (z_1 - z_2) / (c_1 - c_2)$

The session-typed signing protocol makes nonce reuse a compile-time error. Each `FreshNonce` can only be consumed once, and the type system enforces that signing sessions progress linearly through states without backtracking.

## Implementation Security

The implementation includes comprehensive security documentation in `Protocol/Core/Security.lean`:

**Randomness Requirements:** All secret values (shares, nonces, commitment openings) must be sampled from a CSPRNG. Nonce reuse is catastrophic. The session-typed API makes it a compile-time error.

**Side-Channel Considerations:** The specification flags timing-vulnerable functions (Lagrange computation, norm checks). Production implementations must use constant-time primitives. The `ConstantTimeEq` typeclass (in `Security.lean`) marks types requiring constant-time equality comparison.

**Memory Zeroization:** Sensitive values must be securely erased after use. Platform-specific APIs are documented for C, POSIX, Windows, and Rust. The `Zeroizable` typeclass (in `Security.lean`) marks types requiring secure erasure.

**Secret Wrappers:** The `SecretBox` and `NonceBox` types (in `Security.lean`) wrap sensitive values with private constructors, discouraging accidental duplication or exposure. Use `SecretBox.wrap` and `NonceBox.fresh` to create instances.

## Docs Index

1. [Algebraic Setting](001_algebra.md): Algebraic primitives, module structure, lattice instantiations, and semilattice definitions
2. [Key Generation](002_keygen.md): Dealer and distributed key generation with CRDT state, VSS, party exclusion
3. [Signing Protocol](003_signing.md): Two-round signing protocol with session types, rejection sampling
4. [Verification](004_verification.md): Signature verification and threshold context
5. [Extensions](005_extensions.md): Complaints, refresh/repair coordination, rerandomization, type-indexed phases
6. [Protocol Integration](006_integration.md): External context binding, evidence piggybacking, fast-path signing, self-validating shares
7. [Local Rejection Signing](100_configuration.md): Configuration for local rejection sampling bounds
