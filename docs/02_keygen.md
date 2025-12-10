# Key Generation

Key generation produces the master secret and distributes shares among parties. Two modes are supported. A trusted dealer can sample and distribute shares directly. Alternatively parties can run a distributed key generation protocol without trusting any single entity.

Both modes produce additive shares. Each party $P_i$ holds a secret share $s_i \in \mathcal{S}$. The shares sum to the master secret $s = \sum_i s_i$. The corresponding public key is $\mathsf{pk} = A(s)$.

## Key Share Structure

After key generation each party holds a `KeyShare` containing its local view.

```lean
structure KeyShare (S : Scheme) :=
  (pid  : S.PartyId)   -- party identifier
  (sk_i : S.Secret)    -- secret share
  (pk_i : S.Public)    -- public share = A(sk_i)
  (pk   : S.Public)    -- global public key
```

The key share is the persistent credential a signer carries into the signing protocol.

## Trusted Dealer Mode

In trusted dealer mode a single entity generates and distributes all shares. This mode is simpler but requires trust in the dealer.

### Dealer Output Structure

The dealer produces a `DealerShare` for each party and a `DealerTranscript` bundling the complete key material.

```lean
structure DealerShare (S : Scheme) :=
  (pid      : S.PartyId)
  (sk_i     : S.Secret)
  (pk_i     : S.Public)
  (opening  : S.Opening)
  (commitPk : S.Commitment)

structure DealerTranscript (S : Scheme) :=
  (shares : List (DealerShare S))
  (pk     : S.Public)
```

### Dealer Procedure

The dealer proceeds as follows.

1. Sample a short master secret $s \in \mathcal{S}$.
2. For each party $P_i$ sample a short share $s_i \in \mathcal{S}$.
3. Adjust the final share so that $\sum_i s_i = s$.
4. Compute each public share $\mathsf{pk}_i = A(s_i)$.
5. Compute the global public key $\mathsf{pk} = A(s)$.
6. Commit to each public share as $\mathsf{Com}_i = \mathsf{Com}(\mathsf{pk}_i, r_i)$ for random openings $r_i$.
7. Publish the global public key and all commitments.
8. Send each party $P_i$ its secret share $s_i$ over a secure channel.

The pure implementation `dealerKeygen` takes pre-sampled secrets and openings to keep IO/randomness out of the core logic.

### Dealer Correctness

The linearity of $A$ ensures consistency. Since $\sum_i s_i = s$ the sum of public shares equals the global public key.

$$\sum_i \mathsf{pk}_i = \sum_i A(s_i) = A\left(\sum_i s_i\right) = A(s) = \mathsf{pk}$$

Parties can verify this relation after receiving their shares. They compute $A(s_i)$ and check that the published commitment opens correctly.

### Trust Assumption

The dealer learns the master secret $s$. This mode is appropriate when a trusted party exists or when the protocol operates in a setting where the dealer is later destroyed. For stronger security guarantees use distributed key generation.

## Distributed Key Generation

Distributed key generation removes the need for a trusted dealer. Parties jointly generate shares such that no single party learns the master secret. The protocol runs in two rounds with CRDT-mergeable state at each phase.

### Message Types

The DKG protocol uses commit and reveal messages.

```lean
structure DkgCommitMsg (S : Scheme) :=
  (from     : S.PartyId)
  (commitPk : S.Commitment)

structure DkgRevealMsg (S : Scheme) :=
  (from    : S.PartyId)
  (pk_i    : S.Public)
  (opening : S.Opening)
```

### Party State

Each party $P_i$ maintains local state during the protocol.

```lean
structure DkgLocalState (S : Scheme) :=
  (pid    : S.PartyId)
  (sk_i   : S.Secret)
  (pk_i   : S.Public)
  (openPk : S.Opening)
```

The local state contains:
- A secret share $s_i \in \mathcal{S}$ sampled locally.
- An opening value $r_i \in \mathcal{O}$ for the commitment.
- The commitment $\mathsf{Com}_i = \mathsf{Com}(\mathsf{pk}_i, r_i)$ where $\mathsf{pk}_i = A(s_i)$.

### Round 1: Commit

In round one each party commits to its public share.

1. Party $P_i$ samples a short secret share $s_i \in \mathcal{S}$.
2. Compute the public share $\mathsf{pk}_i = A(s_i)$.
3. Sample a random opening $r_i \in \mathcal{O}$.
4. Compute the commitment $\mathsf{Com}_i = \mathsf{Com}(\mathsf{pk}_i, r_i)$.
5. Broadcast the commitment $\mathsf{Com}_i$ to all parties.

Parties wait until they receive commitments from all other participants. The commitment hides the public share until the reveal phase.

### Round 2: Reveal

In round two each party reveals its public share and opening.

1. Party $P_i$ broadcasts the pair $(\mathsf{pk}_i, r_i)$.
2. Each party verifies all received openings.
3. For each received pair $(\mathsf{pk}_j, r_j)$ check that $\mathsf{Com}_j = \mathsf{Com}(\mathsf{pk}_j, r_j)$.
4. If any verification fails the party aborts or files a complaint.

The binding property of the commitment ensures that a dishonest party cannot change its public share after seeing others.

### Aggregation

After successful verification all parties compute the global public key.

$$\mathsf{pk} = \sum_i \mathsf{pk}_i$$

Each party stores the set of all public shares $\{\mathsf{pk}_i\}$ and the global key $\mathsf{pk}$. Secret shares remain private. Only party $P_i$ knows $s_i$.

### Error Handling

Several error conditions may arise during DKG. The implementation provides structured error types.

```lean
inductive DkgError (PartyId : Type) where
  | lengthMismatch : DkgError PartyId
  | duplicatePids  : DkgError PartyId
  | commitMismatch : PartyId → DkgError PartyId
```

**Missing commitment.** If a party does not receive a commitment from $P_j$ within a timeout it marks $P_j$ as absent. The protocol can proceed with the remaining parties if enough are present. Detected via `lengthMismatch`.

**Invalid opening.** If $\mathsf{Com}(\mathsf{pk}_j, r_j) \neq \mathsf{Com}_j$ then party $P_j$ is marked as malicious. Detected via `commitMismatch`.

**Duplicate participants.** If the same party identifier appears twice, detected via `duplicatePids`.

**Inconsistent views.** If parties disagree about which commitments were received they must run a consensus or abort. The protocol assumes a broadcast channel or equivalent.

### Checked Aggregation

The `dkgAggregateChecked` function validates the transcript before computing the global public key.

```lean
def dkgAggregateChecked
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  : Except (DkgError S.PartyId) S.Public
```

It returns either the public key or a structured error identifying the failure mode. The totality theorem ensures this function always returns a result:

```lean
lemma dkgAggregateChecked_total : (result).isOk ∨ (result).isError
```

### Validity Predicate

A transcript is valid when commits and reveals align by party identifier and each opening matches its commitment.

```lean
def dkgValid
  (S : Scheme)
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S)) : Prop :=
  List.Forall2
    (fun c r => c.from = r.from ∧ S.commit r.pk_i r.opening = c.commitPk)
    commits reveals
```

If `dkgAggregateChecked` succeeds, then `dkgValid` holds.

## Threshold Considerations

In a $t$-of-$n$ threshold setting any $t$ parties can sign. The key generation phase produces additive shares. Threshold functionality arises during signing through Lagrange interpolation.

### Lagrange Coefficients

Let $S \subseteq \{1, \ldots, n\}$ be a signing subset with $|S| \geq t$. The Lagrange coefficient for party $i \in S$ is

$$\lambda_i^S = \prod_{j \in S, j \neq i} \frac{j}{j - i}$$

These coefficients satisfy $\sum_{i \in S} \lambda_i^S \cdot s_i = s$ when the shares are derived from a degree $t-1$ polynomial evaluated at points $1, \ldots, n$.

### Additive vs Polynomial Shares

The base protocol uses additive shares where $\sum_i s_i = s$. For $n$-of-$n$ signing this is sufficient. For $t$-of-$n$ signing the shares must encode polynomial structure.

One approach is to run a verifiable secret sharing protocol during DKG. Each party $P_i$ shares its contribution $s_i$ as a polynomial. After aggregation each party holds a share of the sum of polynomials.

An alternative approach uses additive shares with Lagrange adjustment at signing time. The Lagrange coefficients are computed over the active signer set $S$.

## Public Key Verification

Any external verifier can check the consistency of published data.

1. Verify that each commitment $\mathsf{Com}_i$ opens to $\mathsf{pk}_i$.
2. Verify that $\mathsf{pk} = \sum_i \mathsf{pk}_i$.

These checks do not require knowledge of secret shares. They ensure that the published public key corresponds to the committed shares.

## DKG with Complaints

The threshold DKG variant collects complaints when verification fails rather than immediately aborting.

```lean
inductive Complaint (PartyId : Type) where
  | openingMismatch (accused : PartyId)
  | missingReveal (accused : PartyId)
```

The `dkgAggregateWithComplaints` function returns either the public key or a list of complaints.

```lean
def dkgAggregateWithComplaints
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  : Except (List (Complaint S.PartyId)) S.Public
```

This enables exclusion of misbehaving parties while continuing with the honest subset.

## Party Exclusion

After collecting complaints, the protocol computes which parties should be excluded.

```lean
def Complaint.accused : Complaint PartyId → PartyId
  | .openingMismatch p => p
  | .missingReveal p => p

def accusedParties (complaints : List (Complaint PartyId)) : List PartyId :=
  (complaints.map Complaint.accused).dedup

def excludeFaulty (allParties : List PartyId) (complaints : List (Complaint PartyId)) : List PartyId :=
  let faulty := accusedParties complaints
  allParties.filter (fun p => p ∉ faulty)
```

### Quorum Check

For threshold security, enough valid parties must remain:

```lean
inductive ExclusionResult (PartyId : Type)
  | quorumMet (validParties : List PartyId)   -- can continue
  | quorumFailed (validCount : Nat) (needed : Nat)  -- must abort

def hasThresholdQuorum (allParties complaints : List _) (threshold : Nat) : Bool :=
  (excludeFaulty allParties complaints).length ≥ threshold
```

If $|valid| \geq t$, the protocol can continue. Otherwise it must abort.

## Reconstruction from Subset

When some parties are excluded, the remaining valid parties can reconstruct the public key using Lagrange interpolation.

```lean
def dkgLagrangeCoeff [Field F] (pidToScalar : PartyId → F) (validPids : List PartyId) (i : PartyId) : F :=
  let xi := pidToScalar i
  let others := validPids.filter (· ≠ i)
  (others.map (fun j => let xj := pidToScalar j; xj / (xj - xi))).prod

def reconstructPkFromSubset
    (S : Scheme) [Field S.Scalar]
    (pidToScalar : S.PartyId → S.Scalar)
    (validReveals : List (DkgRevealMsg S)) : S.Public :=
  let validPids := validReveals.map (·.sender)
  let weightedPks := validReveals.map fun r =>
    let λ_i := dkgLagrangeCoeff pidToScalar validPids r.sender
    λ_i • r.pk_i
  weightedPks.sum
```

### Full DKG with Exclusion

The `dkgWithExclusion` function combines complaint handling with reconstruction:

```lean
def dkgWithExclusion
    (S : Scheme) [Field S.Scalar]
    (pidToScalar : S.PartyId → S.Scalar)
    (allParties : List S.PartyId)
    (commits : List (DkgCommitMsg S))
    (reveals : List (DkgRevealMsg S))
    (threshold : Nat)
    : Except (List (Complaint S.PartyId) × Nat) (S.Public × List S.PartyId) :=
  let complaints := dkgCheckComplaints S commits reveals
  if complaints.isEmpty then
    -- No complaints: simple aggregation
    Except.ok ((reveals.map (·.pk_i)).sum, allParties)
  else
    -- Try reconstruction from valid subset
    let validParties := excludeFaulty allParties complaints
    if validParties.length ≥ threshold then
      let validReveals := filterValidReveals reveals validParties
      let pk := reconstructPkFromSubset S pidToScalar validReveals
      Except.ok (pk, validParties)
    else
      Except.error (complaints, validParties.length)
```

### Threshold Parameters

```lean
structure DKGParams where
  n : Nat                    -- total parties
  t : Nat                    -- threshold
  threshold_valid : t ≤ n    -- proof that t ≤ n

def DKGParams.maxFaulty (p : DKGParams) : Nat := p.n - p.t

def DKGParams.canContinue (p : DKGParams) (faultyCount : Nat) : Bool :=
  faultyCount ≤ p.maxFaulty
```

## Finalizing Key Shares

After DKG completes successfully, each party converts its local state into a persistent key share.

```lean
def finalizeKeyShare
  (S : Scheme)
  (st : DkgLocalState S)
  (pk : S.Public)
  : KeyShare S :=
{ pid  := st.pid,
  sk_i := st.sk_i,
  pk_i := st.pk_i,
  pk   := pk }
```

## Security Properties

**Secrecy.** No coalition of fewer than $t$ parties learns the master secret $s$.

**Correctness.** Honest execution produces shares that satisfy $A(\sum_i s_i) = \mathsf{pk}$.

**Robustness.** If all parties are honest the protocol terminates successfully. If a party misbehaves it is detected through commitment verification.

**Totality.** The checked aggregation functions always return either success or a structured error.
