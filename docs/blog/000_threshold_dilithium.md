# Threshold Dilithium: FROST-Inspired Post-Quantum Signatures

FROST (Flexible Round-Optimized Schnorr Threshold signatures) demonstrates how to build threshold signatures from Schnorr's linear structure. Dilithium, the lattice-based signature scheme standardized as ML-DSA, shares this linear structure. This post describes how to adapt the FROST approach to the Dilithium setting.

## What FROST Is Really Doing

FROST splits a group secret key into shares using Shamir secret sharing. Each signer holds one share. During signing, each signer contributes a partial signature based on their share and some randomness. An aggregator combines these partials into a single signature indistinguishable from one produced by a single signer.

The key insight is that Schnorr signatures are linear in both the secret key and the nonce. The sum of partial secrets behaves like one secret. The sum of partial nonces behaves like one nonce. FROST exploits this linearity while adding careful bookkeeping to prevent nonce reuse and rogue-key attacks.

## Dilithium in Brief

Dilithium is a linear algebra construction over polynomial rings with carefully managed noise. Keys are vectors over a ring. Signing samples a short random vector y, computes a commitment via matrix multiplication, hashes the commitment with the message to produce a challenge, and combines y with the secret and challenge into a response.

The response must satisfy norm bounds. If the response is too large, the signer rejects and resamples. This rejection sampling prevents information leakage about the secret key. The structure resembles Schnorr lifted into a lattice setting with additional constraints on vector lengths.

## Adapting FROST to Dilithium

The adaptation follows from asking which parts of the signing equation can be split across participants and recombined. The answer mirrors FROST.

We secret-share the key by splitting the secret key vector into additive shares. Each participant holds one share. The shares sum to the full secret key. We distribute randomness by having each signer sample their own piece of the ephemeral vector. The pieces sum to produce the global randomness used in a standard signature.

Reconstruction happens only at the signature level. No signer sees the full secret key or full randomness. The final signature is indistinguishable from one produced by a single signer holding the complete key.

## Protocol Structure

The protocol runs in two rounds following the FROST pattern.

In round one, each signer commits to their randomness and broadcasts the commitment. After collecting all commitments, the group computes a shared challenge by hashing the message and aggregate commitment.

In round two, each signer uses their secret share and randomness share to compute a partial response. The aggregator collects partial responses and sums them into the final response. The resulting signature pairs this response with the aggregate commitment and passes standard Dilithium verification.

## What Changes in the Lattice Setting

Several aspects require more care in Dilithium than in Schnorr.

Rejection sampling becomes distributed. In single-signer Dilithium, the signer rejects and restarts if the response norm is too large. In a threshold setting, rejection must happen locally without requiring distributed coordination. Each signer applies a tighter local bound so that any valid combination of partials satisfies the global bound.

The noise structure is higher-dimensional. Randomness is not a simple scalar but a vector in a polynomial ring. Sharing and combining this randomness while preserving security requires careful design. The commitment and response objects are larger than their Schnorr counterparts.

Communication costs increase. Partial signatures and commitments are vectors or polynomials rather than group elements. The protocol must ensure each participant can complete their work locally without excessive bandwidth.

## Why This Works

The concept is straightforward. FROST works because Schnorr is linear in the secret and nonce. Dilithium signatures are also linear constructions over a module with managed noise. Thresholdizing Dilithium respects this linearity. The secret key equals the sum of shares. The signing randomness equals the sum of shares. The final response equals the sum of partial responses. Everything happens in the same algebraic space as the single-signer scheme.

The verifier sees an ordinary Dilithium signature. The distributed key and randomness are invisible. Verification uses the standard algorithm with no awareness of the threshold structure.

## Practical Considerations

Threshold Dilithium signatures may not be practical for many use cases. Dilithium signatures are substantially larger than ECDSA or Schnorr signatures. A Dilithium2 signature is on the order of 2.5 KB compared to ~64 bytes for ECDSA. Threshold variants do not increase this size, but applications sensitive to signature size should evaluate whether the overhead is acceptable.

The scheme is therefore best suited for contexts where post-quantum security is required and signature size is not the primary constraint.
