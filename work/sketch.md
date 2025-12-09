A *simplified Dilithium-style / lattice-Schnorr* scheme and then turn it into a 2-round, DKG-backed threshold protocol. I’ll deliberately ignore some parameter/proof fine print, but I’ll be honest about every place where we’re sweeping stuff under the rug.

---

## 1. Base (single-signer) lattice “Schnorr-like” scheme

Work over a ring (R_q) (e.g., (\mathbb{Z}_q[x]/(x^n+1))). Let:

* Public matrix: (A \in R_q^{k \times l}) (global parameter)
* Secret key: short vector (s \in R^{l}) (coeffs bounded by some small B)
* Public key:
  [
  \text{pk} = A \cdot s \in R_q^{k}
  ]

**Signing a message (m):**

1. Sample **ephemeral randomness**: short (y \leftarrow D_y \subset R^l).
2. Compute:
   [
   w = A \cdot y \in R_q^k
   ]
3. Compute challenge:
   [
   c = H(m, \text{pk}, w) \in {0,1}^\lambda
   ]
4. Compute response:
   [
   z = y + c \cdot s
   ]
5. If (\lVert z \rVert) too large, reject and restart (this is the Dilithium-style rejection step).

Signature: (\sigma = (z, c)).

**Verification:**

1. Recompute:
   [
   w' = A \cdot z - c \cdot \text{pk} \quad (\text{in } R_q^k)
   ]
2. Check:

   * (\lVert z \rVert) within bound;
   * (c \stackrel{?}{=} H(m, \text{pk}, w')).

If yes, accept.

This is basically the Fiat–Shamir transform of a lattice relation proof (A s = \text{pk}). It’s a clean “Schnorr-ish” structure:

* **Linear in secret**: (z = y + c s).
* **Linear in randomness**: (w = A y).
* Verification equation is linear.

This structure is what we’ll exploit.

---

## 2. DKG: getting shared (s = \sum s_i) and pk

We want (n) parties (P_1,\dots,P_n) with additive shares (s_i) such that:

* Global secret: (s = \sum_i s_i)
* Global public key:
  [
  \text{pk} = A \cdot s = \sum_i A \cdot s_i
  ]

A *high-level* DKG sketch:

1. Each party (P_i) samples short secret share (s_i).
2. Computes its public contribution:
   [
   \text{pk}_i = A \cdot s_i
   ]
3. Broadcasts:

   * Commitment (C_i = \text{Com}(\text{pk}_i, \text{aux}_i))
   * (Optionally) a ZK proof that “(\exists) short (s_i) s.t. (\text{pk}_i = A s_i)” (to prevent malicious huge secrets).
4. After checking all proofs/commitments, everyone sets:
   [
   \text{pk} = \sum_i \text{pk}_i
   ]
   and keeps their local (s_i) forever secret.

With standard VSS / complaint mechanisms, you can make this robust and threshold (e.g., Shamir-share a master secret instead of just additive shares, but additive is simpler to reason about here). For the signing algebra, **all we need is that**:

* Each party holds (s_i),
* Everyone agrees on (\text{pk} = A \cdot \sum_i s_i).

---

## 3. Threshold signing: structure we want

Goal: 2-round FROST-like protocol.

We target that each party (P_i) computes a partial signature (z_i) such that:

* (z = \sum_i z_i) is a valid single-signer response in the base scheme.
* Challenge (c) is global and unique.
* No party learns another’s share (s_j).

Given base scheme:
[
z = y + c s.
]

We’ll distribute:

* (s = \sum_i s_i)
* (y = \sum_i y_i)

then have each party compute:

[
z_i = y_i + c s_i,
]

and the aggregator sets:

[
z = \sum_i z_i.
]

Let’s check the verification equation algebraically:

[
\begin{aligned}
A z - c ,\text{pk}
&= A \left(\sum_i z_i\right) - c \left( \sum_i \text{pk}_i \right) \
&= \sum_i A z_i - c \sum_i A s_i \
&= \sum_i A(y_i + c s_i) - c \sum_i A s_i \
&= \sum_i A y_i + \sum_i A (c s_i) - c \sum_i A s_i \
&= \sum_i A y_i \
&= A \left(\sum_i y_i\right) = w.
\end{aligned}
]

So the combined signature (z) satisfies the same relation as a monolithic signer with (y = \sum_i y_i). That’s the key: **the algebra works perfectly**.

Now we’ll wrap this in a 2-round protocol with commitments, challenges, and aggregation.

---

## 4. 2-round threshold signing protocol

We’ll denote:

* Message: (m)
* Participants for this signing session: subset (S \subseteq {1,\dots,n}).
* Aggregator: can be one of them or external; just responsible for collecting/broadcasting.

### Precomputation / per-session state

For each signing session, each (P_i \in S) does:

1. Sample ephemeral randomness: short (y_i \leftarrow D_y).
2. Compute:
   [
   w_i = A \cdot y_i.
   ]
3. Compute commitment:
   [
   \text{Com}_i = \text{Com}(w_i, r_i),
   ]
   where (r_i) is some random opening nonce.

They keep ((y_i, w_i, r_i)) private for now.

---

### **Round 1 – Commit phase**

Each (P_i \in S):

1. Sends (\text{Com}_i) to the aggregator.

Aggregator:

1. Waits to receive all (\text{Com}_i) for (i \in S).
2. (Optionally) broadcasts the list of commitments and the participant set (S) to everyone (so all know who’s in).

> From signers’ point of view, this is “Round 1: send your nonce commitment; receive the set of commitments / participants.”

---

### **Between rounds – reveal combined (w) and challenge (c)**

We now need a *global* (w) and challenge (c).

**Step A – Reveal (w_i)**
Each (P_i \in S):

1. Sends ((w_i, r_i)) to the aggregator.

Aggregator:

1. Checks that (\text{Com}(w_i, r_i) = \text{Com}_i) for each (i).

   * If any fail → abort / blame that party.
2. Computes global:
   [
   w = \sum_{i \in S} w_i.
   ]
3. Computes challenge:
   [
   c = H(m, \text{pk}, S, {\text{Com}*i}*{i \in S}, w).
   ]
4. Broadcasts (c) to all (P_i \in S).

**Observation:**
This “reveal + challenge” step can be viewed as part of the second round from the *signers’ perspective*:

* They’ve already sent commitments (Round 1).
* They now receive challenge (c), plus possibly the revealed (w_i) or just (w).

Communication-wise, implementations can fold this into 2 logical rounds for signers:

* **Round 1:** send commitments.
* **Round 2:** after aggregator releases (c), send signature shares.

The intermediate “w_i reveal” is just the aggregator’s internal timeline and doesn’t require extra interaction rounds from signers, as long as the network supports these phases.

If you want to be very strict about “message rounds”, you can label this as a 3-phase, 2-round protocol (like FROST does: nonces commit, nonces reveal by aggregator, partial signatures).

---

### **Round 2 – Partial signature phase**

Each (P_i \in S) now knows:

* Its share (s_i),
* Its ephemeral randomness (y_i),
* Global challenge (c).

Each (P_i) computes:

[
z_i = y_i + c s_i
]

(and optionally enforces a per-party loose bound (\lVert z_i \rVert \le B_{\text{local}}) to detect obviously invalid shares).

They send (z_i) to the aggregator.

Aggregator:

1. Receives all (z_i) from (i \in S).
2. Computes:
   [
   z = \sum_{i \in S} z_i.
   ]
3. Forms signature:
   [
   \sigma = (z, c, S).
   ]

---

### Final verification

Anyone verifying uses the *single-signer* verification algorithm:

1. Compute:
   [
   w' = A z - c, \text{pk}.
   ]
2. Check bound (\lVert z \rVert) ≤ (B_{\text{global}}).
3. Check:
   [
   c \stackrel{?}{=} H(m, \text{pk}, S, {\text{Com}*i}*{i \in S}, w').
   ]

If all pass, accept.

By the algebra we checked earlier, if all parties act honestly, we have (w' = w), so the hash matches.

---

## 5. Where the “hard parts” live

So far, we’ve **validated the core idea**:

* Secret shares (s_i) → additive,
* Ephemerals (y_i) → additive,
* Final response (z = \sum (y_i + c s_i)),
* Base verification equation holds exactly.

Now, pathology / realism points:

### (a) Rejection sampling & norm bounds

In a Dilithium-like scheme you normally reject if (\lVert z\rVert) too big. In the threshold setting:

* You don’t want the adversary to learn about the distribution of (s) or (s_i) from repeated rejections.
* You’d like to avoid many aborts post-challenge (which can sometimes be turned into side channels).

Ways to cope (conceptually):

* **Parameter tweak / “always accept” variant:**

  * Make distribution / bounds loose enough that rejection is negligible.
  * You pay in larger sig size but keep the algebra simple.

* **Masking / correlated randomness:**

  * Each party uses:
    [
    z_i = y_i + c s_i + t_i
    ]
    where (\sum_i t_i = 0) (pre-shared masked randomness).
  * Per-party bounds can be looser while still bounding (\lVert z\rVert).
  * Abort behavior leaks essentially only about masks + noise, not about (s_i) individually.

The protocol sketch stays the same; you just modify the internal (z_i) formula and parameter choices.

### (b) Rogue-key resistance

We avoid rogue-key issues by **doing DKG** instead of “local key generation + public key aggregation”:

* No party chooses a key after seeing others’ public keys.
* The DKG enforces that pk is tied to honest or at-least-structured contributions.

If you did want aggregation from independently generated keys, you’d need extra proofs (like in FROST), but the DKG route you specified is actually nicer.

### (c) Threshold t-out-of-n instead of n-out-of-n

Above sketch was implicitly (n)-of-(n). For (t)-of-(n):

* During DKG, Shamir-share a master secret (\alpha) and derive (s_i = f(i)) for a polynomial (f).
* In signing, any subset (S) of size (t) reconstructs an *effective share* with Lagrange coefficients (\lambda_i):

  Each party computes:
  [
  z_i = y_i + c \lambda_i s_i,
  ]
  and aggregator sets:
  [
  z = \sum_{i \in S} z_i = \sum_{i \in S} y_i + c \sum_{i \in S} \lambda_i s_i = y + c s.
  ]

Algebra still works; DKG + complaint handling gets more complex, but it’s standard threshold crypto story.

---

## 6. Did we “validate that it can be done”?

Yes, in the sense you probably care about as a protocol designer:

* We started from a **realistic lattice signing structure** (Fiat–Shamir over (A s = \text{pk})).
* We wrote:

  * a DKG that gives additive shares of (s),
  * a 2-round threshold signing protocol with:

    * commitment to ephemerals (nonces),
    * global challenge from summed commitments,
    * linear partial signatures,
    * aggregation that yields a valid monolithic signature.
* We checked the **verification equation algebra** in detail and it matches the single-signer scheme exactly.
* The “hairy parts” (rejection, leakage, tight proofs) are **engineering and proof work**, not structural impossibilities.

So from a *structures and equations* point of view, a FROST-like, 2-round, DKG-backed lattice threshold scheme is absolutely feasible using a Dilithium-like backbone.
