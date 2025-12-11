# Algebraic Setting

The protocol is parameterized by an abstract scheme structure. This structure defines the algebraic objects and operations. Concrete instantiations choose specific rings and modules.

## Scheme Record

The `Scheme` structure bundles the algebraic setting with cryptographic oracles. It keeps types abstract so proofs and implementations can swap in concrete rings and primitives.

```lean
structure Scheme where
  PartyId   : Type
  Message   : Type
  Secret    : Type
  Public    : Type
  Challenge : Type
  Scalar    : Type

  [scalarSemiring : Semiring Scalar]
  [secretAdd      : AddCommGroup Secret]
  [publicAdd      : AddCommGroup Public]
  [secretModule   : Module Scalar Secret]
  [publicModule   : Module Scalar Public]
  [challengeSMulSecret : SMul Challenge Secret]
  [challengeSMulPublic : SMul Challenge Public]

  A : Secret →ₗ[Scalar] Public

  Commitment : Type
  Opening    : Type
  commit     : Public → Opening → Commitment
  commitBinding : ∀ {x₁ x₂ o₁ o₂}, commit x₁ o₁ = commit x₂ o₂ → x₁ = x₂

  -- Domain-separated hash functions (FROST pattern)
  hashCollisionResistant : Prop
  hashToScalar : ByteArray → ByteArray → Scalar  -- H(domain, data)
  hashDkg : PartyId → Public → Public → Scalar   -- H_dkg for PoK
  hash : Message → Public → List PartyId → List Commitment → Public → Challenge

  -- Optional identifier derivation
  deriveIdentifier : ByteArray → Option PartyId

  normOK : Secret → Prop
```

## Modules and Scalars

Let $R$ denote a commutative semiring with unity. This serves as the scalar ring. Common choices include $\mathbb{Z}_q$ for a prime $q$.

The secret space $\mathcal{S}$ is an additive commutative group. It carries an $R$-module structure. Secrets are elements of $\mathcal{S}$.

The public space $\mathcal{P}$ is also an additive commutative group with an $R$-module structure. Public keys are elements of $\mathcal{P}$.

In lattice instantiations both spaces may be polynomial rings or vectors over $\mathbb{Z}_q$.

## The Linear Map A

The core algebraic structure is a linear map $A : \mathcal{S} \to \mathcal{P}$. This map is $R$-linear. It satisfies

$$A(s_1 + s_2) = A(s_1) + A(s_2)$$

and

$$A(r \cdot s) = r \cdot A(s)$$

for all secrets $s_1, s_2, s \in \mathcal{S}$ and scalars $r \in R$.

The map $A$ connects private shares to their public counterparts. If $s_i$ is a secret share then $\mathsf{pk}_i = A(s_i)$ is the corresponding public share.

Linearity ensures that aggregation in $\mathcal{S}$ corresponds to aggregation in $\mathcal{P}$. The sum of public shares equals the image of the sum of secret shares. This property underlies the threshold aggregation.

### Design Choice: No Explicit Error Term

In Dilithium, the public key includes an error term: $t = As_1 + s_2$ where $s_2$ is small. This makes $t$ indistinguishable from random under MLWE. During verification, Dilithium uses a `HighBits()` function to absorb the error term $c \cdot s_2$.

We deliberately keep the abstract map $A : \mathcal{S} \to \mathcal{P}$ without an explicit error term for these reasons:

1. **Abstraction boundary.** The error term is a key generation detail. Once the public key $t$ is computed, signing and verification only need the linear relationship $A(z) = A(y) + c \cdot A(s_1)$.

2. **HighBits is an implementation detail.** The truncation that absorbs $c \cdot s_2$ can be encoded in the concrete instantiation:
   - The `hash` function can hash `HighBits(w)` rather than full $w$
   - The `normOK` predicate can include the HighBits consistency check

3. **Clean protocol logic.** The signing and verification math stays clean:
   $$z = y + c \cdot s$$
   $$A(z) - c \cdot \mathsf{pk} = A(y) = w$$
   The error handling lives in the concrete instantiation, not the abstract protocol.

4. **Instantiation flexibility.** Different lattice schemes handle errors differently (Dilithium vs Falcon vs others). The abstract Scheme lets each instantiation encode its approach appropriately.

For a Dilithium instantiation, the Scheme record would be configured as:

```lean
def dilithiumScheme (params : DilithiumParams) : Scheme :=
  { Secret := PolyVec params.l      -- s₁ ∈ R_q^l
  , Public := PolyVec params.k      -- t = As₁ + s₂ (precomputed at keygen)
  , A := dilithiumKeyMap            -- maps response z to Az
  , normOK := fun z =>
      dilithiumNormCheck z params ∧
      highBitsConsistent z params   -- both quality checks
  , hash := fun m pk ... w =>
      hashHighBits (highBits w params.gamma2) m  -- hash truncated w
  , ... }
```

The error term $s_2$ is baked into the public key during key generation. The `normOK` predicate enforces both the coefficient bound $\|z\|_\infty < \gamma_1 - \beta$ and the HighBits consistency check. The `hash` function operates on truncated values as Dilithium requires.

## Challenges

The challenge space is a separate type. In typical instantiations challenges are scalars from $R$ or a related ring. Challenges act on secrets and publics via scalar multiplication.

For a challenge $c$ and secret $s$ the product $c \cdot s$ is a secret. For a challenge $c$ and public $p$ the product $c \cdot p$ is a public. This action must be compatible with the module structure.

## Commitments

A commitment scheme binds a public value to a commitment string. Let $\mathsf{Com} : \mathcal{P} \times \mathcal{O} \to \mathcal{C}$ denote the commitment function. Here $\mathcal{O}$ is the opening space and $\mathcal{C}$ is the commitment space.

The binding property requires that

$$\mathsf{Com}(x_1, o_1) = \mathsf{Com}(x_2, o_2) \implies x_1 = x_2$$

for all $x_1, x_2 \in \mathcal{P}$ and $o_1, o_2 \in \mathcal{O}$.

This property ensures that a commitment uniquely determines the committed value. Adversaries cannot produce two different openings for the same commitment.

## Hash Functions

Following FROST, we use domain-separated hash functions for different protocol operations. This prevents cross-protocol attacks where a hash collision in one context could be exploited in another.

### Domain Separation

Each hash function uses a unique domain prefix:

| Domain | FROST Name | Purpose | Prefix |
|--------|------------|---------|--------|
| Binding factor | H1 | Compute binding factors $\rho_i$ | `ice-nine-v1-rho` |
| Challenge | H2 | Fiat-Shamir challenge $c$ | `ice-nine-v1-chal` |
| Nonce | H3 | Nonce derivation | `ice-nine-v1-nonce` |
| Message | H4 | Message pre-hashing | `ice-nine-v1-msg` |
| Commitment list | H5 | Commitment encoding | `ice-nine-v1-com` |
| DKG | HDKG | Proof of knowledge | `ice-nine-v1-dkg` |
| Identifier | HID | Party ID derivation | `ice-nine-v1-id` |

### Challenge Hash (H2)

The primary hash function maps protocol inputs to challenges:

$$H_2 : \mathcal{M} \times \mathcal{P} \times \mathsf{List}(\mathsf{PartyId}) \times \mathsf{List}(\mathcal{C}) \times \mathcal{P} \to \mathcal{Ch}$$

The inputs are the message $m$, the global public key $\mathsf{pk}$, the participant set $S$, the list of commitments, and the aggregated nonce $w$.

### DKG Hash (HDKG)

Used for proof of knowledge in DKG:

$$H_{\text{dkg}} : \mathsf{PartyId} \times \mathcal{P} \times \mathcal{P} \to R$$

Maps (party ID, public key, commitment) to a scalar challenge.

### Identifier Derivation (HID)

The `deriveIdentifier` function maps arbitrary byte strings to party identifiers:

$$H_{\text{id}} : \mathsf{ByteArray} \to \mathsf{Option}(\mathsf{PartyId})$$

Uses domain prefix `ice-nine-v1-id`. Returns `none` if the derived value is zero (invalid identifier).

```lean
-- In Scheme record
deriveIdentifier : ByteArray → Option PartyId := fun _ => none

-- Convenience function
def Scheme.deriveId (S : Scheme) (data : ByteArray) : Option S.PartyId :=
  S.deriveIdentifier data
```

This enables deterministic identifier derivation from human-readable strings or external identifiers.

### Random Oracle Model

In security proofs the hash is modeled as a random oracle. This means it behaves as a uniformly random function. The random oracle model enables simulation-based security arguments.

## Norm Predicate

A norm predicate $\mathsf{normOK} : \mathcal{S} \to \mathsf{Prop}$ gates acceptance. Signatures with large response vectors are rejected.

The predicate captures a bound on the norm of the response. For lattice signatures this prevents leakage through the response distribution. Rejection sampling or abort strategies ensure the bound holds.

In the abstract model the predicate is a parameter. Concrete instantiations define it based on the lattice parameters.

### Dilithium-Style Norm Bounds

For Dilithium-style signatures, the norm check uses:

- $\ell_\infty$ norm: $\|z\|_\infty = \max_i |z_i|$
- Rejection bound: $\|z\|_\infty < \gamma_1 - \beta$ where $\beta = \tau \cdot \eta$

```lean
structure DilithiumParams where
  n      : Nat := 256    -- ring dimension
  q      : Nat := 8380417 -- modulus
  tau    : Nat           -- challenge weight (number of ±1)
  eta    : Nat           -- secret coefficient bound
  gamma1 : Nat           -- nonce coefficient range
  gamma2 : Nat           -- low-bits range

def dilithiumNormOK (p : DilithiumParams) (z : List Int) : Prop :=
  vecInfNorm z < p.gamma1 - p.tau * p.eta
```

Standard parameter sets:

| Level | τ | η | γ₁ | β | Security |
|-------|---|---|-----|---|----------|
| Dilithium2 | 39 | 2 | 2¹⁷ | 78 | 128-bit |
| Dilithium3 | 49 | 4 | 2¹⁹ | 196 | 192-bit |
| Dilithium5 | 60 | 2 | 2¹⁹ | 120 | 256-bit |

## Concrete Scheme Instantiations

The implementation provides several concrete schemes:

### Simple Scheme (Testing)

Identity map over integers. For correctness proofs only.

```lean
def simpleScheme : Scheme :=
  { Secret := Int, Public := Int, A := LinearMap.id, ... }
```

### ZMod Scheme (Field Arithmetic)

Scalar multiplication over $\mathbb{Z}_q$.

```lean
def zmodScheme (q : ℕ) [Fact q.Prime] (a : ZMod q) : Scheme :=
  { Secret := ZMod q, Public := ZMod q, A := LinearMap.lsmul _ _ a, ... }
```

### Matrix Scheme (SIS/LWE)

Matrix-vector multiplication: $A : \mathbb{Z}_q^m \to \mathbb{Z}_q^n$.

```lean
def matrixScheme (n m q : ℕ) (A : Matrix (Fin n) (Fin m) (ZMod q)) : Scheme :=
  { Secret := Fin m → ZMod q
  , Public := Fin n → ZMod q
  , A := matrixMulVecLinear A  -- A(s) = A·s
  , ... }
```

This models the SIS/LWE structure:
- Secret key: $s \in \mathbb{Z}_q^m$ (short vector)
- Public key: $t = A \cdot s \in \mathbb{Z}_q^n$
- Security reduces to SIS: forging requires finding short $z$ with $Az = 0$

### Polynomial Scheme (Ring-LWE)

Polynomial multiplication in $R_q = \mathbb{Z}_q[X]/(X^n + 1)$.

```lean
def polyScheme (n q : ℕ) (a : Fin n → ZMod q) : Scheme :=
  { Secret := Fin n → ZMod q   -- polynomial coefficients
  , Public := Fin n → ZMod q
  , A := polyMulLinear a       -- A(s) = a·s mod (X^n + 1)
  , ... }
```

This models Ring-LWE structure:
- Ring: $R_q = \mathbb{Z}_q[X]/(X^n + 1)$ for $n$ a power of 2
- Multiplication uses negacyclic convolution ($X^n = -1$)
- Efficient via Number Theoretic Transform (NTT)

## Semilattice Structure

Protocol state at each phase forms a join-semilattice. A semilattice is an algebraic structure with a binary join operation $\sqcup$ that is commutative, associative, and idempotent.

$$a \sqcup b = b \sqcup a$$
$$a \sqcup (b \sqcup c) = (a \sqcup b) \sqcup c$$
$$a \sqcup a = a$$

The join induces a partial order: $a \leq b$ iff $a \sqcup b = b$.

### Message Map Semilattice

Protocol messages are stored in `MsgMap` structures—hash maps keyed by sender ID. This design makes conflicting messages from the same sender **un-expressable** at the type level.

```lean
structure MsgMap (S : Scheme) (M : Type*) [BEq S.PartyId] [Hashable S.PartyId] where
  map : Std.HashMap S.PartyId M

instance : Join (MsgMap S M) := ⟨MsgMap.merge⟩
instance : LE (MsgMap S M) := ⟨fun a b => a.map.toList.all (fun (k, _) => b.map.contains k)⟩
```

The merge operation takes the union of keys, keeping the first value on conflict. This provides:

- **Conflict-freedom by construction**: At most one message per sender
- **Commutativity**: Merge order doesn't affect the set of senders
- **Idempotence**: Merging a map with itself is identity
- **Strict mode**: `tryInsert` returns conflict indicators for misbehavior detection

This provides the foundation for merging commit maps, reveal maps, and share maps while preventing Byzantine parties from injecting multiple conflicting messages.

### Product Semilattice

If $\alpha$ and $\beta$ are semilattices, their product $\alpha \times \beta$ is a semilattice under componentwise join.

```lean
instance prodJoin (α β) [Join α] [Join β] : Join (α × β) :=
  ⟨fun a b => (a.1 ⊔ b.1, a.2 ⊔ b.2)⟩
```

This allows combining protocol state with auxiliary data (refresh masks, repair bundles, rerandomization masks).

### CRDT Semantics

Semilattice merge ensures conflict-free replicated data type (CRDT) semantics. Replicas can merge states in any order and converge to the same result. This is essential for handling:

- Out-of-order message delivery
- Network partitions and rejoins
- Concurrent protocol executions

### Instance Constraint Patterns

The protocol modules use consistent instance requirements:

**For HashMap-based structures (MsgMap, NonceRegistry):**
- `[BEq S.PartyId]` - Boolean equality
- `[Hashable S.PartyId]` - Hash function for HashMap

**For decidable equality (if-then-else, match guards):**
- `[DecidableEq S.PartyId]` - Prop-valued equality with decision procedure

**For field arithmetic (Lagrange coefficients):**
- `[Field S.Scalar]` - Division required for λ_i = Π x_j / (x_j - x_i)
- `[DecidableEq S.Scalar]` - For checking degeneracy

## Lagrange Interpolation

The `Protocol/Lagrange.lean` module provides a unified API for computing Lagrange interpolation coefficients used across threshold protocols.

### Core Function

```lean
def coeffAtZero [Field F] [DecidableEq F]
    (partyScalar : F)
    (allScalars : List F)
    : F :=
  let others := allScalars.filter (· ≠ partyScalar)
  others.foldl (fun acc xj => acc * (xj / (xj - partyScalar))) 1
```

This computes $\lambda_i = \prod_{j \neq i} \frac{x_j}{x_j - x_i}$ for evaluating at 0.

### Scheme-Aware API

```lean
def schemeCoeffAtZero (S : Scheme)
    [Field S.Scalar] [DecidableEq S.Scalar] [DecidableEq S.PartyId]
    (pidToScalar : S.PartyId → S.Scalar)
    (allParties : List S.PartyId)
    (party : S.PartyId)
    : S.Scalar

def buildPartyCoeffs (S : Scheme)
    [Field S.Scalar] [DecidableEq S.Scalar] [DecidableEq S.PartyId]
    (pidToScalar : S.PartyId → S.Scalar)
    (parties : List S.PartyId)
    : List (PartyCoeff S)
```

These functions integrate with the Scheme type for protocol use, including batch computation and precomputed coefficient storage.

## Secret Wrappers

Secrets and nonces are wrapped in opaque structures to discourage accidental duplication or exposure.

```lean
/-- Wrapper for secrets with private constructor.
    Forces explicit acknowledgment when accessing secret material. -/
structure SecretBox (α : Type*) where
  private mk ::
  val : α

/-- Wrap a secret value. -/
def SecretBox.wrap (secret : α) : SecretBox α := ⟨secret⟩

/-- Wrapper for nonces to highlight their ephemeral nature.
    Nonce reuse is catastrophic: treat these as single-use. -/
structure NonceBox (α : Type*) where
  private mk ::
  val : α

/-- Create from a freshly sampled nonce. -/
def NonceBox.fresh (nonce : α) : NonceBox α := ⟨nonce⟩
```

The `private` constructors prevent arbitrary creation of wrapped values. Use `SecretBox.wrap` and `NonceBox.fresh` to create instances. This lightweight discipline signals intent—code that accesses the `val` field must explicitly acknowledge it is handling secret material.

Both types have `Zeroizable` and `ConstantTimeEq` marker instances to indicate security requirements for production implementations.

**Key Share Integration:**

```lean
structure KeyShare (S : Scheme) where
  pid  : S.PartyId        -- party identifier
  sk_i : SecretBox S.Secret  -- wrapped secret share
  pk_i : S.Public         -- public share = A(sk_i)
  pk   : S.Public         -- global public key

/-- Create KeyShare from unwrapped secret (use during DKG). -/
def KeyShare.create (S : Scheme) (pid : S.PartyId) (sk : S.Secret) (pk_i pk : S.Public)
    : KeyShare S :=
  { pid := pid, sk_i := ⟨sk⟩, pk_i := pk_i, pk := pk }

/-- Access secret for cryptographic operations. -/
def KeyShare.secret (share : KeyShare S) : S.Secret :=
  share.sk_i.val
```

All protocol code that needs the secret share calls `share.secret` rather than pattern-matching on the `SecretBox`. This creates a clear audit trail for secret access.

## Single-Signer Schnorr Relation

The threshold protocol generalizes the single-signer Schnorr pattern. The single-signer version proceeds as follows.

**Key generation.** Sample a short secret $s \in \mathcal{S}$. Compute the public key $\mathsf{pk} = A(s)$.

**Signing.** Given message $m$:

1. Sample a short ephemeral secret $y \in \mathcal{S}$.
2. Compute the nonce $w = A(y)$.
3. Compute the challenge $c = H(m, \mathsf{pk}, w)$.
4. Compute the response $z = y + c \cdot s$.
5. Output signature $(z, c)$.

**Verification.** Given signature $(z, c)$ and message $m$:

1. Compute $w' = A(z) - c \cdot \mathsf{pk}$.
2. Check $\mathsf{normOK}(z)$.
3. Compute $c' = H(m, \mathsf{pk}, w')$.
4. Accept if $c' = c$.

The threshold protocol distributes $s$ among parties. Each party holds a share $s_i$ with $\sum_i s_i = s$. The signing procedure produces partial responses $z_i$ that aggregate to $z = \sum_i z_i$.
