We’d do this in two big layers:

1. **Crypto / game-based layer**: define security notions (EUF-CMA, threshold EUF-CMA, negligible advantage, etc.) in Lean using a probabilistic model.
2. **Protocol refinement layer**: prove that the threshold protocol is just a “distributed implementation” of the base scheme → same signature distribution ⇒ security transfers.

I’ll walk through how you’d set this up in Lean, with code skeletons.

---

## 1. Fix the base security story

We want to *reuse* the security of the base single-signer scheme. So first, you define:

* Randomized algorithms as `pmf`-valued functions.
* EUF-CMA game for the base scheme.
* Its security assumption as an axiom or separate proof.

### 1.1. Randomness: use `pmf`

Mathlib has `probability_theory.pmf`. Use it as the basic model of randomized algorithms:

```lean
import probability_theory.probability_mass_function

open_locale classical big_operators

/-- A randomized algorithm from α to β. -/
@[reducible] def Rand (α : Type) := pmf α
```

For stateful / oracle algorithms, you can wrap states into the result type or go full “oracle computation” style, but we can start with “stateless randomized functions”.

### 1.2. Negligible functions and advantage

Use the classic negligible definition over a security parameter `κ : ℕ`:

```lean
/-- A function f : ℕ → ℝ is negligible if for every polynomial p, eventually f(k) ≤ 1 / p(k). -/
def negligible (f : ℕ → ℝ) : Prop :=
∀ (p : ℕ → ℝ), (∃ C > 0, ∀ k, p k ≤ C * (k+1)^C) →  -- crude 'polynomial' predicate
  ∀ᶠ k in at_top, f k ≤ 1 / (p k)
```

You can refine “polynomial” later, or postulate a `poly` class.

Define an *advantage function* for a forging adversary as `advantage : ℕ → ℝ`.

---

## 2. Formalize the base scheme and its EUF-CMA game

Assume we have a *single-signer* version of our lattice-Schnorr scheme:

```lean
structure BaseScheme :=
  (secparam : Type)           -- security parameter type, e.g. ℕ
  (Message Public Secret Challenge Signature : Type)

  [addSecret : AddCommGroup Secret]
  [addPublic : AddCommGroup Public]
  [smulSC    : SMul Challenge Secret]
  [smulPC    : SMul Challenge Public]

  (A      : Secret → Public)
  (hash   : secparam → Message → Public → Public → Challenge)

  (KeyGen : secparam → Rand (Secret × Public))
  (Sign   : secparam → Secret → Message → Rand Signature)
  (Verify : secparam → Public → Message → Signature → Prop)
```

Then define the **EUF-CMA game** as a `pmf` over `{true,false}` (“adversary wins?”):

```lean
/-- An EUF-CMA adversary: gets pk, oracle for Sign, outputs (m*,σ*). -/
structure EufCmaAdversary (S : BaseScheme) :=
  (state : Type)
  (init  : S.secparam → Rand (state))        -- initializes internal state given κ
  -- oracle: query a message, get back a signature
  (oracle_step : state → S.Message → Rand (state × S.Signature))
  -- final: output candidate forgery
  (final : state → Rand (S.Message × S.Signature))
```

Now the game:

```lean
def eufCmaGame (S : BaseScheme) (A : EufCmaAdversary S) (k : S.secparam) : Rand Bool := do
  -- Key generation
  let (sk, pk) ← S.KeyGen k
  -- Run adversary, answering signing queries
  let s₀ ← A.init k
  -- You’d need to model many oracle queries; for simplicity assume
  -- some bounded number of queries or a generic “run with oracle” mechanism.
  -- Eventually obtain final state sᶠ:
  let sᶠ ← sorry  -- run oracle interaction
  let (m*, σ*) ← A.final sᶠ
  -- Adversary wins if (m*, σ*) verifies and wasn't queried to the oracle as-is
  return (S.Verify k pk m* σ* ∧ sorry)  -- 'm* not previously signed'
```

Then the **advantage** is:

```lean
def eufCmaAdvantage (S : BaseScheme) (A : EufCmaAdversary S) : S.secparam → ℝ :=
fun k => (eufCmaGame S A k).prob mass_of_true
```

(You’d define `prob mass_of_true` via `pmf` evaluation.)

Security assumption:

```lean
def eufCma_secure (S : BaseScheme) : Prop :=
∀ (A : EufCmaAdversary S), negligible (eufCmaAdvantage S A)
```

For our threshold security proof, **we won’t re-prove this**; we assume it or prove it once for the single-signer lattice scheme.

---

## 3. Lift the threshold scheme to a cryptographic primitive

Now we turn the threshold protocol we sketched into a crypto *scheme* interface like `BaseScheme`, but with key generation implemented via DKG and signing via multi-party protocol.

From the previous messages, we have a `Scheme` + DKG + signing protocol in Lean. Now define:

```lean
structure ThresholdScheme :=
  (base   : BaseScheme)
  (PartyId : Type)
  (n      : ℕ)
  -- interface for DKG producing per-party key shares
  (DkgKeyGen : base.secparam → Rand (Public := base.Public) (Vector (KeyShare_like) n))
  -- threshold signer: interacts with n parties (or subset) and outputs a signature
  (ThresholdSign : base.secparam → Vector KeyShare_like n → base.Message → Rand base.Signature)
  (ThresholdVerify : base.secparam → base.Public → base.Message → base.Signature → Prop)
```

Conceptually:

* `ThresholdSign` is the *distributed* protocol composed into a single randomized algorithm (we treat all honest parties + aggregator as one “big algorithm”).
* `ThresholdVerify` is exactly `base.Verify` on the aggregated sig.

The key **functional correctness lemma** you’ll want in Lean is:

> For any `sk, pk` output by `base.KeyGen`, the distribution of
> `base.Sign k sk m` is *identical* to the distribution of
> `ThresholdSign k shares m`, where the shares come from running `DkgKeyGen` on the same randomness and reconstructing `sk` as sum of shares.

We encode this as equality of `pmf`s.

---

## 4. Model the threshold EUF-CMA game

Define an adversary for the threshold scheme:

```lean
/-- Threshold EUF-CMA adversary. May corrupt some parties. -/
structure ThreshEufCmaAdversary (T : ThresholdScheme) :=
  (state : Type)
  (init  : T.base.secparam → T.base.Public → Rand state)
  -- oracles: signing under threshold protocol, corrupting parties, etc.
  (oracle_step : state → Rand state)
  (final : state → Rand (T.base.Message × T.base.Signature))
```

Game:

```lean
def thresholdEufCmaGame (T : ThresholdScheme) (A : ThreshEufCmaAdversary T)
  (k : T.base.secparam) : Rand Bool := do
  -- Run DKG (inside T.DkgKeyGen)
  let shares ← T.DkgKeyGen k
  let pk := -- derive global pk from shares
    sorry
  let s₀ ← A.init k pk
  -- let sᶠ ← run interaction, giving A access to a signing oracle
  let sᶠ ← sorry
  let (m*, σ*) ← A.final sᶠ
  return (T.ThresholdVerify k pk m* σ* ∧ sorry) -- and m* wasn't signed via oracle
```

Advantage:

```lean
def thresholdEufCmaAdvantage (T : ThresholdScheme) (A : ThreshEufCmaAdversary T)
  : T.base.secparam → ℝ :=
fun k => (thresholdEufCmaGame T A k).prob mass_of_true
```

Security notion:

```lean
def threshold_eufCma_secure (T : ThresholdScheme) : Prop :=
∀ A, negligible (thresholdEufCmaAdvantage T A)
```

---

## 5. Core proof strategy in Lean: simulation & distribution equivalence

Now the *main theorem* you want to prove in Lean is of the form:

```lean
theorem threshold_security_from_base
  (T : ThresholdScheme)
  (Himpl : ∀ k m, 
      -- distributed ThresholdSign is distributionally equal to base.Sign
      pmf.map id (T.ThresholdSign k (someSharesFromDkg k) m)
    = pmf.map id (T.base.Sign k (someSkFromSameDkg k) m))
  (Hbase : eufCma_secure T.base)
  : threshold_eufCma_secure T :=
by
  -- Use Himpl to build a reduction from any threshold adversary A
  -- to a single-signer EUF-CMA adversary A'.
  -- Then apply Hbase.
  ...
```

Of course, we need to refine `Himpl` to talk about *joint* distribution of:

* `(pk, oracle answers, adversary view)` in the threshold world vs single-signer world.

This is where the **“protocol refinement”** takes shape:

### 5.1. Define the “monolithic” world and the “threshold” world as games

Define two games as `Rand (Transcript × Bool)`:

* `G_base(A')`: adversary `A'` talking to a single-signer scheme.
* `G_thresh(A)`: adversary `A` talking to the threshold protocol.

Then you want to construct:

* A mapping from any threshold adversary `A` to a base adversary `A'`, and
* A proof that the distributions of “final transcript and win-bit” are identical or negligibly close.

In Lean:

```lean
/-- A reduction from threshold adversaries to base adversaries. -/
def reduce (T : ThresholdScheme) (A : ThreshEufCmaAdversary T)
  : EufCmaAdversary T.base :=
{ state := A.state,
  init := fun k => do
    -- base gives us (sk, pk); in reduction we *drop sk* and simulate threshold DKG
    let (_, pk) ← T.base.KeyGen k
    A.init k pk,
  oracle_step := fun s m => do
    -- when A requests threshold sign(m),
    -- we query the base signing oracle for Sign(k, sk, m),
    -- then "fake" a threshold transcript that produces that signature.
    ...
  final := A.final
}
```

The crux is to show a **simulation lemma**:

```lean
lemma simulation_lemma
  (T : ThresholdScheme) (A : ThreshEufCmaAdversary T) :
  ∀ k, 
    -- probability adversary A wins in threshold game
    thresholdEufCmaAdvantage T A k
  = eufCmaAdvantage T.base (reduce T A) k :=
by
  -- do a sequence-of-games proof in Lean:
  -- 1. inline DkgKeyGen and ThresholdSign into base.KeyGen and base.Sign
  -- 2. use Himpl: distributed sign ~ monolithic sign
  -- 3. show transcript equality
  ...
```

Then the main theorem is:

```lean
theorem threshold_security_from_base
  (T : ThresholdScheme)
  (Hbase : eufCma_secure T.base)
  : threshold_eufCma_secure T :=
by
  intro A
  -- reduce A to A' using `reduce`
  have h_sim : ∀ k,
    thresholdEufCmaAdvantage T A k
    = eufCmaAdvantage T.base (reduce T A) k :=
    simulation_lemma T A
  -- use base security
  have h_base := Hbase (reduce T A)
  -- rewrite using h_sim and close
  refine ?_
  -- show `negligible (thresholdEufCmaAdvantage T A)`
  -- by rewriting to `negligible (eufCmaAdvantage T.base (reduce T A))`
  -- and applying h_base.
  ...
```

---

## 6. What “fully verify” boils down to in practice

To **fully** verify in Lean (beyond handwaving), you’d need to:

1. **Make the algebraic part rigorous**

   * `A` is a linear map (use `linear_map`).
   * Prove the relation `A z - c•pk = w` holds in the threshold scheme for honest parties.
   * That gives you *correctness*.

2. **Model randomness & independence**

   * Ephemeral `y_i` are independent.
   * Their sum has the right distribution.
   * The distribution of `y = ∑ y_i` matches the single-signer’s `y`.
   * You’ll use `pmf.bind` and lemmas about sums of independent random variables.

3. **Define the exact security games you care about**

   * Do you allow adaptive corruption? adaptive signing? static corruptions?
   * That changes how you structure the oracle interface.

4. **Prove distributional equivalence**

   * Show that the view of any (t-bounded) adversary interacting with the threshold protocol is indistinguishable (or identical) to a view interacting with a single-signer oracle.
   * This is usually the longest part in Lean: lots of “rewrite under pmf.bind / associativity / commutativity of sums”.

5. **Plug into base security**

   * Once you’ve reduced `thresholdEufCmaAdvantage` to `eufCmaAdvantage` of some derived adversary `A'`, the rest is a one-liner: apply base security + negligible closure lemmas.
