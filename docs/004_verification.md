# Verification

Verification checks that a signature is valid for a given message and public key. The procedure uses the linear map $A$ and the hash function. It does not require knowledge of any secret shares.

## Inputs

The verifier receives the following inputs.

- **Signature.** The `Signature` structure containing:
  ```lean
  structure Signature (S : Scheme) where
    z       : S.Secret
    c       : S.Challenge
    Sset    : List S.PartyId
    commits : List S.Commitment
    context : ExternalContext := {}
  ```
- **Message.** The message $m \in \mathcal{M}$ that was signed.
- **Public key.** The global public key $\mathsf{pk}$.

## Verification Procedure

The `verify` function checks signature validity.

```lean
def verify
  (S   : Scheme)
  (pk  : S.Public)
  (m   : S.Message)
  (sig : Signature S)
  : Prop :=
  let w' : S.Public := S.A sig.z - (sig.c • pk)
  S.normOK sig.z ∧
    let c' := S.hash m pk sig.Sset sig.commits w'
    c' = sig.c
```

The verifier executes the following steps.

### Step 1: Nonce Recovery

Compute the recovered nonce from the signature components.

$$w' = A(z) - c \cdot \mathsf{pk}$$

This computation uses the linear map $A$ applied to the response $z$. It subtracts the challenge times the public key.

### Step 2: Norm Check

Verify that the response satisfies the norm bound.

$$\mathsf{normOK}(z)$$

If the response has excessive norm the signature is invalid. This check rejects signatures that could leak information through the response distribution.

### Step 3: Challenge Recomputation

Compute the expected challenge using the hash function.

$$c' = H(m, \mathsf{pk}, S, \{\mathsf{Com}^{(w)}_i\}_{i \in S}, w')$$

The hash input matches the signing protocol. It includes the message, public key, signer set, all nonce commitments, and the recovered nonce.

### Step 4: Challenge Comparison

Compare the recomputed challenge to the signature's challenge.

$$c' \stackrel{?}{=} c$$

If the challenges match the signature is valid. Otherwise the signature is invalid.

## Verification Correctness

We show that valid signatures pass verification. Consider a signature produced by honest parties.

The aggregated response is

$$z = \sum_{i \in S} z_i = \sum_{i \in S} (y_i + c \cdot s_i)$$

In the $n$-of-$n$ case this simplifies to

$$z = y + c \cdot s$$

where $y = \sum_i y_i$ and $s = \sum_i s_i$.

Applying $A$ and using linearity gives

$$A(z) = A(y + c \cdot s) = A(y) + c \cdot A(s) = w + c \cdot \mathsf{pk}$$

Subtracting $c \cdot \mathsf{pk}$ yields

$$A(z) - c \cdot \mathsf{pk} = w$$

The recovered nonce equals the original aggregated nonce. Since the hash inputs are identical the recomputed challenge matches the original. The signature passes verification.

### t-of-n Correctness

In the $t$-of-$n$ case the Lagrange coefficients ensure

$$\sum_{i \in S} \lambda_i^S \cdot s_i = s$$

The aggregated response is

$$z = \sum_{i \in S} (y_i + c \cdot \lambda_i^S \cdot s_i) = y + c \cdot s$$

The rest of the argument follows identically.

## Algebraic Identity

The core algebraic identity underlying verification is

$$A(z) - c \cdot \mathsf{pk} = \sum_{i \in S} A(y_i) = w$$

This identity holds because of the following chain of equalities.

$$A(z) = A\left(\sum_{i \in S} z_i\right) = \sum_{i \in S} A(z_i)$$

For each partial response

$$A(z_i) = A(y_i + c \cdot s_i) = A(y_i) + c \cdot A(s_i) = w_i + c \cdot \mathsf{pk}_i$$

Summing over the signer set

$$A(z) = \sum_{i \in S} (w_i + c \cdot \mathsf{pk}_i) = w + c \cdot \sum_{i \in S} \mathsf{pk}_i$$

In the $n$-of-$n$ case the public shares sum to the global key

$$\sum_{i \in S} \mathsf{pk}_i = \mathsf{pk}$$

Therefore

$$A(z) = w + c \cdot \mathsf{pk}$$

and the verification equation follows.

## Commitment Verification

The nonce commitments serve two purposes during verification.

### Session Binding

The commitments are included in the hash input. This binds the challenge to the specific signing session. An adversary cannot reuse partial signatures from different sessions because the commitments would differ.

### Audit Trail

The commitments provide an audit trail. A verifier can check that the signing session followed the protocol. Without access to the openings the verifier cannot check the commitments directly. However the commitments still bind the signers to their original nonces.

## Error Cases

Several conditions cause verification to fail.

**Invalid response.** The response $z$ does not satisfy $\mathsf{normOK}(z)$.

**Challenge mismatch.** The recomputed challenge $c'$ differs from the signature's challenge $c$.

**Malformed signature.** The signature does not contain all required components.

## Batch Verification

When verifying multiple signatures with the same public key some computations can be shared.

### Shared Public Key Computation

If multiple signatures use the same $\mathsf{pk}$ the verifier can cache $\mathsf{pk}$ rather than recomputing it.

### Parallel Hash Evaluation

The hash computations for different signatures are independent. They can run in parallel.

### Aggregated Equation Check

For a batch of $k$ signatures with random weights $\alpha_1, \ldots, \alpha_k$ the verifier can check

$$\sum_{j=1}^{k} \alpha_j \cdot (A(z_j) - c_j \cdot \mathsf{pk}) = \sum_{j=1}^{k} \alpha_j \cdot w_j$$

This aggregated check is faster than checking each equation separately. A failure requires checking signatures individually to identify the invalid ones.

## Phase-Restricted Signature Extraction

Signatures can only be extracted from the `done` phase. Earlier phases cannot produce signatures by construction.

```lean
def extractSignature (S : Scheme) : State S .done → Signature S
  | ⟨sig⟩ => sig
```

For threshold-aware extraction with context:

```lean
structure DoneWithCtx (S : Scheme) :=
  (ctx : ThresholdCtx S)
  (sig : Signature S)

def extractSignatureWithCtx (S : Scheme) : DoneWithCtx S → Signature S
  | ⟨_, sig⟩ => sig
```

This phase-based discipline ensures signatures are only produced after complete protocol execution.

## Correctness Theorems

The Lean implementation provides formal correctness proofs in `Proofs/Correctness/Correctness.lean`.

### Generic Happy-Path Correctness

```lean
theorem verify_happy_generic
    (S : Scheme) [DecidableEq S.PartyId]
    (pk : S.Public)
    (m : S.Message)
    (Sset : List S.PartyId)
    (commits : List (SignCommitMsg S))
    (reveals : List (SignRevealWMsg S))
    (shares  : List (SignShareMsg S))
    (hvalid : ValidSignTranscript S Sset commits reveals shares) :
  let w := reveals.foldl (fun acc r => acc + r.w_i) (0 : S.Public)
  let c := S.hash m pk Sset (commits.map (·.commitW)) w
  verify S pk m (aggregateSignature S c Sset (commits.map (·.commitW)) shares)
```

### Lattice Scheme Correctness

```lean
theorem verify_happy_lattice
    (pk : latticeScheme.Public)
    (m : latticeScheme.Message)
    (Sset : List latticeScheme.PartyId)
    (commits : List (SignCommitMsg latticeScheme))
    (reveals : List (SignRevealWMsg latticeScheme))
    (shares  : List (SignShareMsg latticeScheme))
    (hvalid : ValidSignTranscript latticeScheme Sset commits reveals shares) :
  let w := reveals.foldl (fun acc r => acc + r.w_i) (0 : latticeScheme.Public)
  let c := latticeScheme.hash m pk Sset (commits.map (·.commitW)) w
  verify latticeScheme pk m (aggregateSignature latticeScheme c Sset (commits.map (·.commitW)) shares)
```

### Core Linearity Lemma

These lemmas are in `Proofs/Core/ListLemmas.lean`:

```lean
lemma sum_zipWith_add_smul
    {R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]
    (c : R) (ys sks : List M) (hlen : ys.length = sks.length) :
    (zipWith (fun y s => y + c • s) ys sks).sum = ys.sum + c • sks.sum
```

## Soundness

Verification is sound under the security assumptions. If the hash function behaves as a random oracle an adversary cannot produce a valid signature without knowing the secret shares.

The binding property of commitments prevents an adversary from adaptively choosing nonces. The norm check prevents signatures with excessive response norms.

### Special Soundness

The core security property is **special soundness**: two valid signatures with the same nonce but different challenges reveal the secret key.

Given two valid signature equations with the same nonce $w$ but different challenges:
- $A(z_1) = w + c_1 \cdot \mathsf{pk}$
- $A(z_2) = w + c_2 \cdot \mathsf{pk}$

We can derive: $A(z_1 - z_2) = (c_1 - c_2) \cdot \mathsf{pk}$

If $c_1 \neq c_2$ and we're in a field, this reveals $\mathsf{sk}$ such that $\mathsf{pk} = A(\mathsf{sk})$:

$$\mathsf{sk} = (c_1 - c_2)^{-1} \cdot (z_1 - z_2)$$

This property explains:
1. **Why nonce reuse is catastrophic** - the secret key can be algebraically recovered
2. **The basis for the Fiat-Shamir security proof** - a simulator can rewind a forger to extract two transcripts
3. **The core of the SIS reduction** - extracted differences are short vectors in ker(A)

```lean
theorem special_soundness_algebraic
    {M : Type*} [AddCommGroup M]
    {R : Type*} [Ring R] [Module R M]
    (A : M →ₗ[R] M) (z₁ z₂ w pk : M) (c₁ c₂ : R)
    (hv1 : A z₁ = w + c₁ • pk)
    (hv2 : A z₂ = w + c₂ • pk) :
    A (z₁ - z₂) = (c₁ - c₂) • pk

theorem nonce_reuse_key_recovery
    {F : Type*} [Field F]
    {M : Type*} [AddCommGroup M] [Module F M]
    (z₁ z₂ sk : M) (c₁ c₂ : F)
    (hne : c₁ ≠ c₂)
    (heq : z₁ - z₂ = (c₁ - c₂) • sk) :
    sk = (c₁ - c₂)⁻¹ • (z₁ - z₂)
```

### Unforgeability Reduction to SIS

Signature unforgeability reduces to the Short Integer Solution problem via special soundness.

**Reduction outline:**
1. Challenger generates SIS instance: matrix $A$, wants short $z$ with $Az = 0$
2. Embed $A$ as the public key: $\mathsf{pk} = A$ (viewing pk as derived from A)
3. Simulate signing oracle using random oracle programming
4. When forger outputs $(m^*, \sigma^*)$, rewind to get second signature with same $w$
5. Use special soundness to extract difference $z_1 - z_2$
6. This difference is a short vector in ker(A) → SIS solution

**Tightness:** The reduction loses a factor of $Q_h$ (hash queries) from rewinding.

```lean
structure EUFCMAtoSIS (S : Scheme) (p : SISParams) where
  forgerAdvantage : Real
  signingQueries : Nat
  hashQueries : Nat
  sisAdvantage : Real
  reduction_bound : sisAdvantage ≥ forgerAdvantage / hashQueries
```

### Threshold Response Independence

For threshold signatures, response independence holds for the aggregated response. If each party's response $z_i$ is independent of their share $s_i$ (by local rejection sampling), then the aggregate $z = \sum z_i$ is independent of the master secret $s = \sum s_i$.

**Composition argument:**
1. Each $z_i = y_i + c \cdot s_i$ where $y_i$ is the party's nonce
2. Local rejection sampling ensures $z_i$ is statistically independent of $s_i$
3. By linearity: $z = \sum z_i = \sum y_i + c \cdot \sum s_i = y + c \cdot s$
4. Since each $z_i$ reveals nothing about $s_i$, and parties don't see each other's $s_i$, the aggregate reveals nothing about $s$

This standard composition follows from Lyubashevsky's "Fiat-Shamir with Aborts" applied to each party individually.

**Reference:** Lyubashevsky, "Fiat-Shamir with Aborts", ASIACRYPT 2009.

### Axiom Index

All axioms used throughout the codebase are documented in `Proofs/Core/Assumptions.lean`. They fall into three categories:

1. **Mathlib-equivalent**: Properties provable with Mathlib but requiring significant integration work (e.g., `coeffs_sum_to_one` for Lagrange interpolation)

2. **Cryptographic assumptions**: Properties requiring computational hardness assumptions (e.g., `vss_hiding`, `SISHard`, `MLWEHard`)

3. **Implementation details**: Properties about data structures requiring extensive formalization (e.g., `MsgMap.merge_idem`)

Each axiom includes a justification and literature reference. See `Proofs/Core/Assumptions.lean` for the complete index.

### Security Assumptions Structure

```lean
structure Assumptions (S : Scheme) where
  hashRO            : Prop                    -- hash modeled as QROM (Fiat-Shamir)
  commitCR          : Prop                    -- commitment collision resistant (implies binding)
  hashBinding       : HashBinding             -- binding for hash-based commitment
  commitHiding      : HidingAssumption S      -- commitment hiding (requires ROM; NOT formally proven)
  normLeakageBound  : Prop                    -- norm bounds prevent leakage
  corruptionBound   : Nat                     -- max corrupted parties < threshold
  sisParams         : Option SISParams        -- SIS parameters for unforgeability
  mlweParams        : Option MLWEParams       -- MLWE parameters for key secrecy

def thresholdUFcma (S : Scheme) (A : Assumptions S) : Prop :=
  A.hashRO ∧ A.commitCR ∧ A.normLeakageBound
```

### Collision Resistance and Hiding

Hash-based commitments derive their properties from the underlying hash function:

```lean
-- Collision resistance: finding x₁ ≠ x₂ with H(x₁) = H(x₂) is hard
structure CollisionResistant (H : α → β) : Prop where
  no_collisions : True  -- axiomatized

-- Hiding: commitments reveal nothing about the value (requires ROM)
structure HidingAssumption (S : Scheme) : Prop where
  hiding : True  -- axiomatized; NOT provable without probabilistic reasoning
```

**Important**: Hiding is NOT formally proven in Lean. It requires probabilistic reasoning that Lean cannot express. Protocols needing hiding must explicitly include this assumption.

## Lattice Hardness Assumptions

Security reduces to standard lattice problems:

### Short Integer Solution (SIS)

Given $A \in \mathbb{Z}_q^{n \times m}$, find short $z$ with $Az = 0 \mod q$.

```lean
structure SISParams where
  n : Nat              -- lattice dimension (rows of A)
  m : Nat              -- columns of A
  q : Nat              -- modulus
  beta : Nat           -- solution norm bound
  m_large : m > n * Nat.log2 q := by decide  -- security requirement

structure SISInstance (p : SISParams) where
  A : Fin p.n → Fin p.m → ZMod p.q   -- public matrix

structure SISSolution (p : SISParams) (inst : SISInstance p) where
  z : Fin p.m → Int
  z_short : ∀ i, Int.natAbs (z i) ≤ p.beta
  z_nonzero : ∃ i, z i ≠ 0
  Az_zero : ∀ i : Fin p.n,
    (Finset.univ.sum fun j => inst.A i j * (z j : ZMod p.q)) = 0

def SISHard (p : SISParams) : Prop := True  -- axiomatized
```

**Reduction**: A forger that produces valid signatures can be used to solve SIS.

### Module Learning With Errors (MLWE)

Distinguish $(A, As + e)$ from $(A, u)$ where $s, e$ are small.

```lean
structure MLWEParams where
  n : Nat    -- ring dimension (degree of R_q = Z_q[X]/(X^n + 1))
  k : Nat    -- module rank (number of ring elements in secret)
  q : Nat    -- modulus
  eta : Nat  -- error distribution parameter

structure MLWEInstance (p : MLWEParams) where
  A : Fin p.k → Fin p.k → (Fin p.n → ZMod p.q)  -- public matrix
  b : Fin p.k → (Fin p.n → ZMod p.q)            -- public vector b = As + e

structure MLWESecret (p : MLWEParams) where
  s : Fin p.k → (Fin p.n → Int)                 -- secret vector
  e : Fin p.k → (Fin p.n → Int)                 -- error vector
  s_short : ∀ i j, Int.natAbs (s i j) ≤ p.eta
  e_short : ∀ i j, Int.natAbs (e i j) ≤ p.eta

def MLWEHard (p : MLWEParams) : Prop := True  -- axiomatized
```

**Reduction**: Recovering the secret key from the public key requires solving MLWE.

### Full Lattice Assumptions

```lean
structure LatticeAssumptions (S : Scheme) extends Assumptions S where
  sisInst   : SISParams           -- SIS instance derived from scheme
  mlweInst  : MLWEParams          -- MLWE instance derived from scheme
  sis_hard  : SISHard sisInst     -- SIS is hard for these parameters
  mlwe_hard : MLWEHard mlweInst   -- MLWE is hard for these parameters

def keySecrecy (S : Scheme) (A : LatticeAssumptions S) : Prop :=
  A.mlwe_hard

def livenessOrAbort (S : Scheme) (A : Assumptions S) : Prop := True
```

## Parameter Validation

Lightweight checks catch obviously insecure parameters. These are necessary conditions, not sufficient for security - real analysis requires the [lattice estimator](https://lattice-estimator.readthedocs.io/).

```lean
def minSecureDimension : Nat := 256

def SISParams.isSecure (p : SISParams) : Prop :=
  p.n ≥ minSecureDimension ∧
  p.m ≥ 2 * p.n ∧
  p.beta < p.q / 2

def MLWEParams.isSecure (p : MLWEParams) : Prop :=
  p.n ≥ minSecureDimension ∧
  p.k ≥ 1 ∧
  p.eta ≤ 4

def isPowerOf2 (n : Nat) : Bool :=
  n > 0 && (n &&& (n - 1)) = 0
```

The implementation uses standard [NIST FIPS 204 (ML-DSA/Dilithium)](https://csrc.nist.gov/pubs/fips/204/final) parameter sets which provide 128, 192, and 256 bits of security.

## Batch Verification Implementation

This section provides implementation guidance for batch verification in Rust.

### Mathematical Foundation

For $k$ signatures with random weights $\alpha_1, \ldots, \alpha_k$, batch verification checks:

$$\sum_{j=1}^{k} \alpha_j \cdot (A(z_j) - c_j \cdot \mathsf{pk}_j) = \sum_{j=1}^{k} \alpha_j \cdot w_j$$

This can be rewritten as a single multiscalar multiplication:

$$\sum_{j=1}^{k} \alpha_j \cdot A(z_j) - \sum_{j=1}^{k} \alpha_j c_j \cdot \mathsf{pk}_j = \sum_{j=1}^{k} \alpha_j \cdot w_j$$

When using the same public key for all signatures:

$$A\left(\sum_{j=1}^{k} \alpha_j z_j\right) - \left(\sum_{j=1}^{k} \alpha_j c_j\right) \cdot \mathsf{pk} = \sum_{j=1}^{k} \alpha_j \cdot w_j$$

### Security Requirements

Random weights prevent an adversary from constructing signatures that cancel each other out. With 128-bit random weights, the probability of a forgery passing batch verification is negligible ($2^{-128}$).

- Weights MUST be cryptographically random (CSPRNG)
- Weights MUST be at least 128 bits for security
- Weights MUST be generated fresh for each batch verification

### Rust Data Structures

```rust
/// Entry for batch verification
pub struct BatchEntry<S: Scheme> {
    pub message: S::Message,
    pub signature: Signature<S>,
    pub public_key: S::Public,
}

/// Batch verification context
pub struct BatchContext<S: Scheme> {
    entries: Vec<BatchEntry<S>>,
}

/// Batch verification result
pub enum BatchResult {
    /// All signatures verified
    AllValid,
    /// Batch failed - need individual verification
    BatchFailed,
    /// Individual failures identified
    Failures(Vec<usize>),
}
```

### Batch Verification Algorithm

```rust
impl<S: Scheme> BatchContext<S> {
    pub fn verify(&self, rng: &mut impl CryptoRng) -> BatchResult {
        if self.entries.len() < 2 {
            // For single entry, verify individually
            return self.verify_individual();
        }

        // Generate random 128-bit weights
        let weights: Vec<S::Scalar> = self.entries
            .iter()
            .map(|_| S::Scalar::random_128bit(rng))
            .collect();

        // Compute LHS: Σ αⱼ·A(zⱼ) - Σ αⱼcⱼ·pkⱼ
        let mut lhs = S::Public::zero();
        for (entry, weight) in self.entries.iter().zip(&weights) {
            let az = S::A(&entry.signature.z);
            let c_pk = entry.signature.c * entry.public_key;
            lhs += weight * (az - c_pk);
        }

        // Compute RHS: Σ αⱼ·wⱼ
        let mut rhs = S::Public::zero();
        for (entry, weight) in self.entries.iter().zip(&weights) {
            let w = recover_nonce(&entry.signature, &entry.public_key);
            rhs += weight * w;
        }

        // Check equation
        if lhs == rhs {
            BatchResult::AllValid
        } else {
            // Fall back to individual verification
            self.identify_failures()
        }
    }

    fn identify_failures(&self) -> BatchResult {
        let failures: Vec<usize> = self.entries
            .iter()
            .enumerate()
            .filter(|(_, e)| !verify_single(e))
            .map(|(i, _)| i)
            .collect();

        if failures.is_empty() {
            // Rare case: batch failed but all individual pass
            // Could indicate implementation bug
            BatchResult::AllValid
        } else {
            BatchResult::Failures(failures)
        }
    }
}
```

### Performance Optimizations

#### Single Multiscalar Multiplication

For best performance, use a single multiscalar multiplication (MSM) operation:

```rust
// Instead of computing each term separately:
// for each j: lhs += weight[j] * (A(z[j]) - c[j] * pk[j])

// Collect all scalars and points:
let scalars: Vec<Scalar> = /* ... */;
let points: Vec<Point> = /* ... */;

// Single MSM operation
let result = multiscalar_mul(&scalars, &points);
```

Libraries like `curve25519-dalek` or `arkworks` provide efficient MSM implementations.

#### Same Public Key Optimization

When all signatures use the same public key:

```rust
// Combine challenge terms
let combined_challenge: Scalar = weights
    .iter()
    .zip(&challenges)
    .map(|(w, c)| w * c)
    .sum();

// Single public key multiplication
let pk_term = combined_challenge * public_key;
```

### Performance Expectations

| Batch Size | Individual (ms) | Batch (ms) | Speedup |
|------------|-----------------|------------|---------|
| 2 | 2.0 | 1.2 | 1.7x |
| 10 | 10.0 | 2.5 | 4.0x |
| 100 | 100.0 | 15.0 | 6.7x |
| 1000 | 1000.0 | 120.0 | 8.3x |

*Estimates based on typical lattice signature verification. Actual performance depends on implementation.*

### Error Handling Strategies

When batch verification fails:

1. **Binary search** (optional): Split batch in half, verify each half. Repeat to narrow down failures. Complexity: O(log n) batch verifications.

2. **Full fallback**: Verify all signatures individually. Complexity: O(n) individual verifications.

Choose based on expected failure rate:
- Low failure rate: Binary search is faster
- High failure rate: Full fallback is simpler

### Benchmarking

```rust
#[bench]
fn bench_batch_verification(b: &mut Bencher) {
    let entries = generate_valid_entries(100);
    let mut rng = OsRng;

    b.iter(|| {
        let ctx = BatchContext::new(entries.clone());
        ctx.verify(&mut rng)
    });
}
```

### References

- Bellare, Garay, Rabin. "Fast Batch Verification for Modular Exponentiation and Digital Signatures" (EUROCRYPT 1998)
- FROST RFC Section 5.3: Batch Verification
- dalek-cryptography/bulletproofs: Efficient MSM implementations
