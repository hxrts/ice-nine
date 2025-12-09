# Verification

Verification checks that a signature is valid for a given message and public key. The procedure uses the linear map $A$ and the hash function. It does not require knowledge of any secret shares.

## Inputs

The verifier receives the following inputs.

- **Signature.** The tuple $\sigma = (z, c, S, \{\mathsf{Com}^{(w)}_i\}_{i \in S})$.
- **Message.** The message $m \in \mathcal{M}$ that was signed.
- **Public key.** The global public key $\mathsf{pk}$.

## Verification Procedure

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

## Soundness

Verification is sound under the security assumptions. If the hash function behaves as a random oracle an adversary cannot produce a valid signature without knowing the secret shares.

The binding property of commitments prevents an adversary from adaptively choosing nonces. The norm check prevents signatures with excessive response norms.

The formal soundness proof lives in the Lean verification modules. It follows the standard Schnorr signature security argument adapted for the threshold setting.
