# Verification

Verification checks that a signature is valid for a given message and public key. The procedure uses the linear map $A$ and the hash function. It does not require knowledge of any secret shares.

## Inputs

The verifier receives the following inputs.

- **Signature.** The `Signature` structure containing:
  ```lean
  structure Signature (S : Scheme) :=
    (z       : S.Secret)
    (c       : S.Challenge)
    (Sset    : List S.PartyId)
    (commits : List S.Commitment)
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

The Lean implementation provides formal correctness proofs.

### Happy-Path Correctness (Integer Scheme)

```lean
theorem verify_happy_simple
    (ys sks : List Int)
    (m : ByteArray)
    (Sset : List Nat)
    (session fromId : Nat)
    (B : Int := 1000) :
  let scheme := simpleSchemeBounded B
  let pk : Int := sks.sum
  let w  : Int := ys.sum
  let c  : Int := scheme.hash m pk Sset [] w
  let shares : List (SignShareMsg scheme) := ...
  let sig : Signature scheme := aggregateSignature scheme c Sset [] shares
  verify scheme pk m sig
```

### Happy-Path Correctness (ZMod Vector Scheme)

```lean
theorem verify_happy_zmod_vec
    {q n : Nat} [Fact q.Prime]
    (ys sks : List (Fin n → ZMod q))
    (m : ByteArray)
    (Sset : List Nat)
    (session fromId : Nat) :
  let S := zmodVecScheme q n
  -- ... similar structure ...
  verify S pk m sig
```

### Core Linearity Lemma

```lean
lemma sum_zipWith_add_smul
    {R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]
    (c : R) :
  ∀ (ys sks : List M),
    (List.zipWith (fun y s => y + c • s) ys sks).sum
      = ys.sum + c • sks.sum
```

## Soundness

Verification is sound under the security assumptions. If the hash function behaves as a random oracle an adversary cannot produce a valid signature without knowing the secret shares.

The binding property of commitments prevents an adversary from adaptively choosing nonces. The norm check prevents signatures with excessive response norms.

The formal soundness proof lives in the Lean verification modules. It follows the standard Schnorr signature security argument adapted for the threshold setting.

### Axiom Index

All axioms used throughout the codebase are documented in `Security/Assumptions.lean`. They fall into three categories:

1. **Mathlib-equivalent**: Properties provable with Mathlib but requiring significant integration work (e.g., `coeffs_sum_to_one` for Lagrange interpolation)

2. **Cryptographic assumptions**: Properties requiring computational hardness assumptions (e.g., `vss_hiding`, `SISHard`, `MLWEHard`)

3. **Implementation details**: Properties about data structures requiring extensive formalization (e.g., `MsgMap.merge_idem`)

Each axiom includes a justification and literature reference. See `Security/Assumptions.lean` for the complete index.

### Security Assumptions Structure

```lean
structure Assumptions (S : Scheme) where
  hashRO : Prop                        -- hash modeled as random oracle (Fiat-Shamir)
  commitCR : Prop                      -- commitment is collision resistant (implies binding)
  commitHiding : HidingAssumption S    -- commitment hiding (requires ROM)
  normLeakageBound : Prop              -- norm bounds prevent leakage
  corruptionBound : Nat                -- max corrupted parties < threshold
  sisParams : Option SISParams         -- SIS parameters for unforgeability
  mlweParams : Option MLWEParams       -- MLWE parameters for key secrecy

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
  n : Nat              -- rows (dimension)
  m : Nat              -- columns
  q : Nat              -- modulus
  beta : Nat           -- solution norm bound
  m_large : m > n * Nat.log2 q  -- security requirement

structure SISSolution (p : SISParams) (inst : SISInstance p) where
  z : Fin p.m → Int
  z_short : ∀ i, Int.natAbs (z i) ≤ p.beta
  z_nonzero : ∃ i, z i ≠ 0
  Az_zero : ∀ i, (Finset.univ.sum fun j => inst.A i j * (z j)) = 0

def SISHard (p : SISParams) : Prop := True  -- axiomatized
```

**Reduction**: A forger that produces valid signatures can be used to solve SIS.

### Module Learning With Errors (MLWE)

Distinguish $(A, As + e)$ from $(A, u)$ where $s, e$ are small.

```lean
structure MLWEParams where
  n : Nat    -- ring dimension (power of 2)
  k : Nat    -- module rank
  q : Nat    -- modulus
  eta : Nat  -- error bound

def MLWEHard (p : MLWEParams) : Prop := True  -- axiomatized
```

**Reduction**: Recovering the secret key from the public key requires solving MLWE.

### Full Lattice Assumptions

```lean
structure LatticeAssumptions (S : Scheme) extends Assumptions S where
  sisInst : SISParams
  mlweInst : MLWEParams
  sis_hard : SISHard sisInst
  mlwe_hard : MLWEHard mlweInst

def keySecrecy (S : Scheme) (A : LatticeAssumptions S) : Prop :=
  A.mlwe_hard
```

## Parameter Validation

Lightweight checks catch obviously insecure parameters:

```lean
def SISParams.isSecure (p : SISParams) : Prop :=
  p.n ≥ 256 ∧ p.m ≥ 2 * p.n ∧ p.beta < p.q / 2

def MLWEParams.isSecure (p : MLWEParams) : Prop :=
  p.n ≥ 256 ∧ isPowerOf2 p.n ∧ p.k ≥ 1 ∧ p.eta ≤ 4

structure SecuritySummary where
  sisValid : Bool
  mlweValid : Bool
  sisSecurityBits : Nat
  mlweSecurityBits : Nat
  overallSecurityBits : Nat
```

The implementation uses standard [NIST FIPS 204 (ML-DSA/Dilithium)](https://csrc.nist.gov/pubs/fips/204/final) parameter sets which provide 128, 192, and 256 bits of security.
