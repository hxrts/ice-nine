# Security Assumptions

The protocol's security rests on several cryptographic assumptions. These assumptions enable the security proofs. Weakening any assumption may compromise the protocol.

## Commitment Binding

The commitment scheme must satisfy the binding property.

### Definition

A commitment scheme is binding if no efficient adversary can produce a collision. Formally the following probability is negligible.

$$\Pr\left[\mathsf{Com}(x_1, o_1) = \mathsf{Com}(x_2, o_2) \land x_1 \neq x_2\right] \leq \mathsf{negl}(\lambda)$$

Here $\lambda$ is the security parameter.

### Role in the Protocol

Binding commitments prevent a party from changing its value after committing. In DKG a party commits to its public share before seeing others. In signing a party commits to its nonce before seeing other nonces.

Without binding an adversary could wait to see other contributions. It could then choose its contribution adaptively to manipulate the outcome.

### Concrete Instantiation

Common binding commitment schemes include hash-based commitments. The commitment is $\mathsf{Com}(x, o) = H(x \| o)$ for a hash function $H$. Binding follows from collision resistance of $H$.

## Random Oracle Model

The hash function is modeled as a random oracle.

### Definition

A random oracle is a function that behaves as a truly random function. For each new query it returns a uniformly random output. For repeated queries it returns the same output.

The random oracle is an idealization. Real hash functions are deterministic. The random oracle model assumes the hash behaves as if it were random.

### Role in the Protocol

The hash function produces challenges from protocol inputs. In the random oracle model the challenge is unpredictable until the inputs are fixed. This prevents an adversary from predicting or influencing the challenge.

The security proof simulates the hash function. The simulator can program the outputs to match the adversary's view. This simulation technique underlies the forking lemma and related arguments.

### Limitations

The random oracle model is not a standard cryptographic assumption. Some schemes secure in the random oracle model are insecure when instantiated with any hash function. This gap is theoretical. In practice random oracle proofs provide strong evidence of security.

### Concrete Instantiation

The protocol should use a hash function from a secure family. SHA-3 and BLAKE3 are suitable choices. The output length should match the security level.

## Norm Bound Satisfaction

The norm predicate must be satisfied with overwhelming probability during honest execution.

### Definition

The norm predicate $\mathsf{normOK} : \mathcal{S} \to \mathsf{Prop}$ accepts elements with bounded norm. The bound $B$ is a protocol parameter.

$$\mathsf{normOK}(z) \iff \|z\| \leq B$$

### Role in the Protocol

Lattice signatures require bounded responses. Without bounds an adversary could extract information about the secret from the response distribution.

Honest signers produce responses of the form $z_i = y_i + c \cdot s_i$. The nonce $y_i$ is sampled short. The product $c \cdot s_i$ is also short if $s_i$ is short. The sum remains short with high probability.

### Rejection Sampling

Some protocols use rejection sampling to ensure the bound. The signer checks if $\|z_i\| \leq B$. If not it aborts and retries with a fresh nonce.

The bound $B$ must be large enough that rejection is rare. The protocol requires

$$\Pr[\|y + c \cdot s\| > B] \leq \mathsf{negl}(\lambda)$$

### Parameter Selection

The norm bound depends on the lattice parameters. Larger bounds increase signature size. Smaller bounds increase rejection probability. The parameters must balance security and efficiency.

## Adversary Model

The adversary is computationally bounded and corrupts a limited number of parties.

### Corruption Threshold

In a $t$-of-$n$ threshold setting the adversary corrupts at most $t-1$ parties. With $t$ or more corrupted parties the adversary can reconstruct the secret and forge signatures.

### Static vs Adaptive Corruption

In the static corruption model the adversary chooses which parties to corrupt before the protocol begins. In the adaptive model the adversary can corrupt parties during execution based on observed messages.

The protocol as specified is secure against static corruption. Adaptive security may require additional techniques such as proactive refresh.

### Network Model

The adversary controls the network. It can delay and reorder messages. It cannot forge messages from honest parties. Secure channels prevent the adversary from reading private messages.

### Computational Bound

The adversary runs in probabilistic polynomial time. It cannot solve computationally hard problems such as finding short vectors in lattices.

## Lattice Assumptions

Security ultimately reduces to lattice hardness assumptions.

### Short Integer Solution (SIS)

The SIS problem asks to find a short nonzero vector $x$ such that $A \cdot x = 0 \mod q$. For appropriate parameters this problem is hard.

### Learning With Errors (LWE)

The LWE problem distinguishes $(A, A \cdot s + e)$ from uniform when $s$ and $e$ are short. This assumption underlies the hiding property of lattice commitments.

### Module Variants

In practice the protocol uses module variants of these assumptions. The linear map $A$ operates on polynomial rings rather than vectors. This reduces key sizes and improves efficiency.

### Hardness Reductions

The security of SIS and LWE reduces to worst-case lattice problems. Finding short vectors in random lattices is as hard as finding short vectors in the hardest lattices of the same dimension.

## Security Goals

Under the assumptions above the protocol achieves the following goals.

### Unforgeability

No efficient adversary can produce a valid signature without the cooperation of at least $t$ parties. This holds even if the adversary sees polynomially many signatures.

### Robustness

If all parties are honest the protocol terminates successfully. Misbehaving parties are detected through commitment verification.

### Privacy

The signature reveals nothing about individual shares. It only reveals that some subset of at least $t$ parties participated.

## Formal Verification

The security proofs are formalized in Lean. The proofs check that the protocol satisfies the security goals under the stated assumptions. The formalization provides machine-checked confidence in the arguments.

### Proof Structure

The Lean proofs are organized as follows.

- `Security/Correctness.lean`: Proves that valid signatures pass verification.
- `Security/Lagrange.lean`: Proves properties of Lagrange interpolation.
- `Security/Robustness.lean`: Proves detection of misbehavior.
- `Security/Assumptions.lean`: Defines the cryptographic assumptions.

### Verification Benefits

Formal verification catches subtle errors that informal proofs may miss. It also documents the precise assumptions required for each theorem.
