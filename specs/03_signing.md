# Two-Round Threshold Signing

The signing protocol produces a threshold signature from partial contributions. It runs in two rounds. The first round commits to ephemeral nonces. The second round produces partial signatures. An aggregator combines the partials into a final signature.

## Inputs

Each signing session requires the following inputs.

- **Message.** The message $m \in \mathcal{M}$ to be signed.
- **Signer set.** The active signing subset $S \subseteq \{1, \ldots, n\}$.
- **Secret shares.** Each party $P_i \in S$ holds its secret share $s_i$.
- **Public key.** All parties know the global public key $\mathsf{pk}$.
- **Public shares.** All parties know the public shares $\{\mathsf{pk}_j\}$ from key generation.

## Party State

Each party $P_i$ maintains local state during signing.

- The ephemeral secret $y_i \in \mathcal{S}$ sampled for this session.
- The ephemeral public value $w_i = A(y_i)$.
- The commitment opening $\rho_i \in \mathcal{O}$.
- The nonce commitment $\mathsf{Com}^{(w)}_i = \mathsf{Com}(w_i, \rho_i)$.
- Received commitments from other parties.
- Received nonces from other parties after reveal.

## Round 1: Nonce Commitment

In round one each party commits to an ephemeral nonce. This commitment prevents adaptive attacks where an adversary chooses its nonce after seeing others.

### Procedure

Each party $P_i \in S$ executes the following steps.

1. Sample a short ephemeral secret $y_i \in \mathcal{S}$.
2. Compute the ephemeral public nonce $w_i = A(y_i)$.
3. Sample a random opening $\rho_i \in \mathcal{O}$.
4. Compute the commitment $\mathsf{Com}^{(w)}_i = \mathsf{Com}(w_i, \rho_i)$.
5. Broadcast the commitment $\mathsf{Com}^{(w)}_i$ to all parties in $S$.
6. Store the local state $(y_i, w_i, \rho_i)$.

### Waiting for Commits

Each party waits until it receives commitments from all other parties in $S$. If a commitment does not arrive within a timeout the party may abort or exclude the missing party.

## Nonce Reveal and Challenge Computation

After all commitments are received parties reveal their nonces and compute the shared challenge.

### Reveal Phase

Each party $P_i$ broadcasts the pair $(w_i, \rho_i)$.

### Verification

Each party verifies all received openings. For each $P_j \in S$ check that

$$\mathsf{Com}(w_j, \rho_j) = \mathsf{Com}^{(w)}_j$$

If any opening is invalid the party aborts the session. It may also file a complaint identifying the misbehaving party.

### Nonce Aggregation

After successful verification compute the aggregated nonce.

$$w = \sum_{i \in S} w_i$$

### Challenge Derivation

Compute the challenge using the hash function.

$$c = H(m, \mathsf{pk}, S, \{\mathsf{Com}^{(w)}_i\}_{i \in S}, w)$$

The challenge depends on the message, public key, signer set, all commitments, and the aggregated nonce. Including the commitments in the hash input binds the challenge to the commit phase.

## Round 2: Partial Signatures

In round two each party produces its partial signature.

### n-of-n Case

In the $n$-of-$n$ setting all parties must participate. Each party $P_i$ computes its partial signature as

$$z_i = y_i + c \cdot s_i$$

This is the standard Schnorr response. The ephemeral secret masks the product of challenge and secret share.

### t-of-n Case

In the $t$-of-$n$ setting a subset of parties signs. Each party must adjust its contribution using Lagrange coefficients.

Let $\lambda_i^S$ denote the Lagrange coefficient for party $i$ over the signing set $S$. Party $P_i$ computes

$$z_i = y_i + c \cdot \lambda_i^S \cdot s_i$$

The Lagrange coefficient ensures that the sum of adjusted shares equals the master secret.

### Lagrange Coefficient Computation

The Lagrange coefficient for party $i$ over set $S$ is

$$\lambda_i^S = \prod_{j \in S, j \neq i} \frac{j}{j - i}$$

This computation uses party identifiers as evaluation points. All arithmetic is in the scalar ring $R$.

### Norm Check

Before broadcasting the partial signature each party may check the norm.

$$\mathsf{normOK}(z_i)$$

If the norm exceeds the bound the party aborts this session. It can retry with a fresh nonce. This check prevents leakage through the response distribution.

### Broadcasting Partials

Each party $P_i$ broadcasts its partial signature $z_i$ to all parties in $S$.

## Aggregation

An aggregator collects all partial signatures and produces the final signature.

### Collecting Partials

The aggregator receives $z_i$ from each $P_i \in S$. If any partial is missing the aggregator may wait or abort.

### Signature Computation

Compute the aggregated response.

$$z = \sum_{i \in S} z_i$$

### Final Signature

The signature consists of the following components.

$$\sigma = (z, c, S, \{\mathsf{Com}^{(w)}_i\}_{i \in S})$$

The signature includes the aggregated response, the challenge, the signer set, and all nonce commitments.

## Correctness

The aggregated response satisfies the verification equation. Consider the $n$-of-$n$ case.

$$z = \sum_{i \in S} z_i = \sum_{i \in S} (y_i + c \cdot s_i) = \sum_{i \in S} y_i + c \cdot \sum_{i \in S} s_i = y + c \cdot s$$

where $y = \sum_i y_i$ and $s = \sum_i s_i$.

Applying the linear map $A$ gives

$$A(z) = A(y) + c \cdot A(s) = w + c \cdot \mathsf{pk}$$

Rearranging yields

$$A(z) - c \cdot \mathsf{pk} = w$$

The verifier recomputes $w$ from this equation and checks the challenge.

### t-of-n Correctness

In the $t$-of-$n$ case the Lagrange coefficients ensure

$$\sum_{i \in S} \lambda_i^S \cdot s_i = s$$

The rest of the argument follows as above.

## Session Binding

The challenge binds to the specific session through several mechanisms.

1. The message $m$ is included in the hash input.
2. The public key $\mathsf{pk}$ is included.
3. The signer set $S$ is included.
4. All nonce commitments are included.
5. The aggregated nonce $w$ is included.

This binding prevents cross-session attacks where an adversary reuses partial signatures from different sessions.

## Abort Conditions

The signing protocol may abort under several conditions.

**Missing commitment.** A party in $S$ does not broadcast its commitment.

**Invalid opening.** A received opening does not match its commitment.

**Missing partial.** A party does not broadcast its partial signature.

**Norm violation.** A partial signature fails the norm check.

**Inconsistent challenge.** Parties compute different challenges due to inconsistent views.

When aborting parties should discard all session state. They should not reuse the ephemeral nonce $y_i$ in any future session.

## Security Considerations

**Nonce reuse.** Using the same nonce $y_i$ in two sessions leaks the secret share $s_i$. Each session must use fresh randomness.

**Commitment binding.** The commitment prevents a party from choosing its nonce adaptively. This protects against rogue key attacks.

**Challenge entropy.** The hash function must produce challenges with sufficient entropy. In the random oracle model this is guaranteed.

**Norm bounds.** The norm check prevents statistical leakage of the secret through the response distribution. Proper bounds depend on the lattice parameters.
