At a high level: proving EUF-CMA for the threshold scheme (via reduction to the base scheme) is *great*, but it’s nowhere near the full story. For a threshold lattice scheme there are a bunch of other things worth formalizing if you really want to sleep well.

I’ll group them into buckets and say how they’d look in Lean.

---

## 1. Core “crypto hygiene” properties

These are more basic than full security, but they catch design bugs.

### a) Correctness

> If all honest parties follow the protocol, verification always accepts.

In Lean: you already basically have this as the algebra lemma:

```lean
theorem correctness
  (S : Scheme)
  (pk : S.Public) (m : S.Message)
  (honest_transcript : HonestTranscript S pk m)
  : verify S pk m (signature_of_transcript honest_transcript) = true
```

Where `HonestTranscript` encodes that:

* DKG was run honestly,
* all signers used the prescribed `y_i`, `w_i`, `z_i` equations.

This proof is mostly linear-algebra and the `A z - c•pk = w` identity.

### b) Uniqueness / non-malleability of signatures

Especially in Schnorr-like schemes: given pk and m, a valid signature σ is (almost) unique.

In Lean:

```lean
theorem signature_uniqueness
  (pk : Public) (m : Message)
  (σ₁ σ₂ : Signature)
  (h1 : Verify k pk m σ₁)
  (h2 : Verify k pk m σ₂)
  : σ₁ = σ₂
```

You might only get *computational* uniqueness, but even a weaker lemma (“if c is fixed then z is determined”) is already useful in proofs.

---

## 2. Threshold-specific security notions

You want to go beyond “just” EUF-CMA to *threshold* EUF-CMA with explicit robustness parameters.

### a) t-out-of-n unforgeability

Current picture: “adversary shouldn’t forge if it controls fewer than t parties.”

Formalize in Lean as:

```lean
def threshold_unforgeable (T : ThresholdScheme) (t : ℕ) : Prop :=
∀ (A : ThreshEufCmaAdversary T),
  (A_corrupts_at_most t) →
  negligible (thresholdEufCmaAdvantage T A)
```

You’d then refine your main theorem to target this property directly (your reduction will need to account for the adversary’s ability to corrupt parties and see shares).

### b) Robustness against malicious signers (no bad shares)

If up to t signers send garbage, honest ones should either:

* still produce a valid signature, or
* detect / blame a misbehaving party.

In Lean: define a “robustness” property on the protocol:

```lean
def robust_signing (T : ThresholdScheme) (t : ℕ) : Prop :=
∀ k pk m (adversarial_behavior : ModelOfMaliciousSigners t),
  -- either:
  (∃ σ, ThresholdVerify k pk m σ)
  -- or:
  (∃ pid, Misbehaved pid adversarial_behavior)
```

This forces you to formalize:

* What a malicious signer can do in each round.
* What counts as “misbehavior” in the transcript.

---

## 3. DKG security properties

The DKG is *critical*. Proving it “secure” typically means several things:

### a) Correctness and agreement

All honest parties derive the same `pk` and consistent shares.

```lean
theorem dkg_correctness
  (honest_parties : Set PartyId)
  (transcript : DkgTranscript S honest_parties)
  : ∀ i j ∈ honest_parties,
      (final_pk i transcript) = (final_pk j transcript)
```

### b) Secrecy / indistinguishability of the secret key

Adversary view of DKG (minus corrupted parties’ shares) should not reveal `s` beyond `pk`.

In Lean: a distributional equivalence/indistinguishability statement:

```lean
theorem dkg_key_hiding
  (k : secparam)
  (Aview : Rand AdversaryView)
  :
  -- View in real DKG world
  dist_real_DKG k Aview
  ≈
  -- View in ideal world where pk is sampled with hidden sk
  dist_ideal_DKG k Aview
```

Where `≈` is computational indistinguishability. You’d encode it as:
for all PPT distinguishers D, their distinguishing advantage is negligible.

### c) Bias-freeness of pk

Adversary shouldn’t be able to bias pk away from the distribution of a “normal” key.

In Lean, another indistinguishability lemma:

```lean
theorem dkg_pk_distribution
  (k : secparam) :
  pk_distribution_from_DKG k
  = pk_distribution_from_KeyGen k
```

(equal as `pmf`s, or computationally indistinguishable).

---

## 4. Abort, leakage & rejection behavior

For lattice schemes, rejection sampling / aborts are a big deal.

### a) No leakage from aborts

Roughly: the adversary’s view of the secret, conditioned on “protocol aborted” vs “protocol succeeded”, should be negligibly different.

In Lean:

```lean
theorem abort_leakage_bound
  (A : ThreshEufCmaAdversary T)
  : negligible (fun k =>
      |Pr[abort & adversary_view] - Pr[abort & ideal_view]|)
```

You can simplify and prove something like:

* Rejection probability is negligibly affected by s.
* So the conditional distribution of transcripts given “accept” is still hiding s.

### b) Bounded advantage from repeated aborts

If the adversary can force retries, show this doesn’t give non-negligible extra info.

This likely becomes a “hybrid game” argument where each retry is modeled and you bound the cumulative leakage.

---

## 5. Privacy of shares & forward secrecy

### a) Share privacy

Even if some subset is corrupted, the remaining honest shares must remain hidden.

In Lean: a statement about the view of an adversary knowing some subset of `sk_i` but not the others:

```lean
theorem share_privacy
  (C : Set PartyId) (|C| < t)
  : adversary_view_with_corrupted_shares C
  ≈ adversary_view_with_dummy_shares C
```

Where “dummy shares” are fresh random short vectors consistent with the same pk.

### b) Forward secrecy (optional)

If you model key refresh / proactive schemes:

* prove that old signatures remain unbreakable even if future shares are exposed.

---

## 6. Composability / UC style

If you’re ambitious: show the protocol *realizes* an ideal threshold-signing functionality `F_ts` in the UC framework.

In Lean, that means:

* Define `F_ts` as an ideal functionality:
  “On input (Sign, m) from a party set S, output a signature that will verify under pk.”
* Define real-world execution of your protocol in an environment Z with adversary A.
* Prove there exists a simulator S such that:

```lean
def realizes (Π : Protocol) (F : Functionality) : Prop :=
∀ Z, ∀ A, ∃ S,
  exec_real Z A Π ≈ exec_ideal Z S F
```

For threshold signing, this is *the* gold standard: it gives you composition guarantees (e.g., safe to use inside larger protocols like threshold ECDSA analogues, MPC, etc.).

---

## 7. Assumption-level reductions (LWE / SIS)

Right now we’ve treated the base scheme (lattice-Schnorr/Dilithium-like) as a black box with EUF-CMA security. If you want Lean to go all the way down:

1. Formalize LWE / SIS problem instances.
2. Define adversaries for these assumptions.
3. Show: “If an adversary breaks base signature EUF-CMA, we can build an adversary that solves LWE/SIS.”

Then, for the threshold scheme, your final theorems look like:

```lean
theorem threshold_secure_under_SIS_LWE
  (T : ThresholdScheme_from_lattice)
  :
  (SIS_hard ∧ LWE_hard) →
  threshold_eufCma_secure T
```

This gives a complete *end-to-end chain* from lattice assumptions to threshold unforgeability.

---

## 8. Implementation-related properties (if you dare)

Some things are *very* hard to do in Lean, but conceptually nice:

* Constant-time behavior / side-channel resilience (requires cost semantics).
* Correct randomness use (no reuse of `y_i` across sessions).
* Type-level guarantees that you *cannot* accidentally reuse nonces (e.g., a linear type or uniqueness token for each `y_i`).

You can at least:

* Encode nonces as an indexed type `Nonce session pid`, so Lean prevents re-use across sessions in the model.

---

## Summary

On top of your main “threshold EUF-CMA via reduction” theorem, the big-ticket items that are worth proving in Lean (or at least modeling) are:

1. **Correctness & uniqueness** of signatures.
2. **Threshold EUF-CMA** with explicit `t` and corruptions.
3. **DKG security**: agreement, key hiding, unbiased pk.
4. **Abort / rejection safety**: negligible leakage from aborts.
5. **Share privacy** for honest parties below threshold.
6. **(Optionally) UC-style composability** via an ideal functionality proof.
7. **(Optionally) Assumption-level reductions** from LWE/SIS.
