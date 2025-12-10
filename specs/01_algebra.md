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
  commitBinding : ...
  hash       : Message → Public → List PartyId → List Commitment → Public → Challenge
  normOK     : Secret → Prop
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

## Challenges

The challenge space is a separate type. In typical instantiations challenges are scalars from $R$ or a related ring. Challenges act on secrets and publics via scalar multiplication.

For a challenge $c$ and secret $s$ the product $c \cdot s$ is a secret. For a challenge $c$ and public $p$ the product $c \cdot p$ is a public. This action must be compatible with the module structure.

## Commitments

A commitment scheme binds a public value to a commitment string. Let $\mathsf{Com} : \mathcal{P} \times \mathcal{O} \to \mathcal{C}$ denote the commitment function. Here $\mathcal{O}$ is the opening space and $\mathcal{C}$ is the commitment space.

The binding property requires that

$$\mathsf{Com}(x_1, o_1) = \mathsf{Com}(x_2, o_2) \implies x_1 = x_2$$

for all $x_1, x_2 \in \mathcal{P}$ and $o_1, o_2 \in \mathcal{O}$.

This property ensures that a commitment uniquely determines the committed value. Adversaries cannot produce two different openings for the same commitment.

## Hash Function

The hash function maps protocol inputs to challenges. Its signature is

$$H : \mathcal{M} \times \mathcal{P} \times \mathsf{List}(\mathsf{PartyId}) \times \mathsf{List}(\mathcal{C}) \times \mathcal{P} \to \mathcal{Ch}$$

The inputs are the message $m$, the global public key $\mathsf{pk}$, the participant set $S$, the list of commitments, and the aggregated nonce $w$.

In security proofs the hash is modeled as a random oracle. This means it behaves as a uniformly random function. The random oracle model enables simulation-based security arguments.

## Norm Predicate

A norm predicate $\mathsf{normOK} : \mathcal{S} \to \mathsf{Prop}$ gates acceptance. Signatures with large response vectors are rejected.

The predicate captures a bound on the norm of the response. For lattice signatures this prevents leakage through the response distribution. Rejection sampling or abort strategies ensure the bound holds.

In the abstract model the predicate is a parameter. Concrete instantiations define it based on the lattice parameters.

## Semilattice Structure

Protocol state at each phase forms a join-semilattice. A semilattice is an algebraic structure with a binary join operation $\sqcup$ that is commutative, associative, and idempotent.

$$a \sqcup b = b \sqcup a$$
$$a \sqcup (b \sqcup c) = (a \sqcup b) \sqcup c$$
$$a \sqcup a = a$$

The join induces a partial order: $a \leq b$ iff $a \sqcup b = b$.

### List Semilattice

Lists form a semilattice under append. The join of two lists is their concatenation. The order is subset inclusion (all elements of $a$ appear in $b$).

```lean
instance : Join (List α) := ⟨List.append⟩
instance : LE (List α) := ⟨fun a b => ∀ x, x ∈ a → x ∈ b⟩
```

This provides the foundation for merging commit lists, reveal lists, and share lists.

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

## Secret Wrappers

Secrets and nonces are wrapped in opaque structures to discourage accidental duplication or exposure.

```lean
structure SecretBox (α : Type) where
  val : α

structure NonceBox (α : Type) where
  val : α
```

This lightweight discipline signals intent. Code that pattern-matches on these wrappers must explicitly acknowledge it is handling secret material.

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
