# Extensions

The core protocol supports several extensions. These extensions address operational requirements beyond basic signing. They enable share management and enhanced privacy. All extension state structures form semilattices that merge via join.

## Complaints

The complaint mechanism identifies misbehaving parties. It activates when protocol invariants are violated.

### Complaint Types

```lean
inductive Complaint (PartyId : Type) where
  | openingMismatch (accused : PartyId)
  | missingReveal (accused : PartyId)
```

### Complaint Triggers

A party files a complaint under the following conditions.

**Invalid commitment opening.** Party $P_j$ reveals a pair $(\mathsf{pk}_j, r_j)$ that does not match its commitment $\mathsf{Com}_j$. Generates `openingMismatch`.

**Missing message.** Party $P_j$ fails to send a required message within the timeout. Generates `missingReveal`.

**Inconsistent session.** The participant set $S$ differs from the expected set.

**Invalid partial signature.** Party $P_j$ produces a partial signature $z_j$ that fails verification.

### Aggregation with Complaints

```lean
def dkgAggregateWithComplaints
  (S : Scheme) [DecidableEq S.PartyId]
  (commits : List (DkgCommitMsg S))
  (reveals : List (DkgRevealMsg S))
  : Except (List (Complaint S.PartyId)) S.Public
```

Returns either the public key or a list of complaints. If aggregation succeeds, the pk equals the sum of revealed public shares.

### Complaint Resolution

When a party files a complaint the protocol may proceed in different ways.

**Abort.** All parties discard the current session. They may retry with a new session excluding the accused party.

**Exclude.** The accused party is removed from the participant set. The remaining parties continue if the threshold is still met.

**Penalize.** In applications with economic stakes the accused party may lose a deposit or face other penalties.

### Complaint Verification

A complaint is verifiable when it includes evidence. For a commitment opening failure the evidence is the commitment, the revealed pair, and a proof that they do not match. Other parties can independently verify the complaint.

## Share Refresh

Share refresh updates the shares without changing the public key. This procedure provides proactive security. Even if an adversary compromises old shares the refreshed shares are independent.

### Mask Function Structure

Masks are represented as functions from party identifier to secret.

```lean
structure MaskFn (S : Scheme) :=
  (mask : S.PartyId → S.Secret)

instance (S : Scheme) : Join (MaskFn S) :=
  ⟨fun a b => { mask := fun pid => a.mask pid + b.mask pid }⟩
```

The join merges masks by pointwise addition.

### Zero-Sum Mask Invariant

The zero-sum property is captured in a dependent structure.

```lean
structure ZeroSumMaskFn (S : Scheme) (active : Finset S.PartyId) :=
  (fn : MaskFn S)
  (sum_zero : (active.toList.map (fun pid => fn.mask pid)).sum = 0)

instance (S : Scheme) (active : Finset S.PartyId) : Join (ZeroSumMaskFn S active)
```

Merging zero-sum masks preserves zero-sum on the same active set.

### Refresh Overview

Each party $P_i$ holds a share $s_i$. After refresh each party holds a new share $s'_i = s_i + \delta_i$. The masks $\delta_i$ sum to zero.

$$\sum_i \delta_i = 0$$

This ensures the master secret is unchanged.

$$\sum_i s'_i = \sum_i (s_i + \delta_i) = \sum_i s_i + \sum_i \delta_i = s + 0 = s$$

### Refresh Function

```lean
def refreshShares
  (S : Scheme)
  (m : MaskFn S)
  (shares : List (KeyShare S)) : List (KeyShare S) :=
  shares.map (fun ks =>
    let sk' := ks.sk_i + m.mask ks.pid
    let pk' := S.A sk'
    { ks with sk_i := sk', pk_i := pk' })
```

### Mask Generation

The masks must sum to zero. One approach is as follows.

1. Each party $P_i$ samples a random mask contribution $\mu_i \in \mathcal{S}$.
2. Parties run a protocol to compute a common offset $\mu = \sum_i \mu_i$.
3. Each party sets $\delta_i = \mu_i - \mu / n$ in a way that ensures $\sum_i \delta_i = 0$.

An alternative uses pairwise contributions. Party $P_i$ sends $\delta_{ij}$ to party $P_j$ and receives $\delta_{ji}$ from $P_j$. The net contribution is $\delta_i = \sum_{j \neq i} (\delta_{ij} - \delta_{ji})$. These contributions cancel pairwise.

### Public Share Update

After refresh each party computes its new public share.

$$\mathsf{pk}'_i = A(s'_i) = A(s_i + \delta_i) = A(s_i) + A(\delta_i) = \mathsf{pk}_i + A(\delta_i)$$

The global public key remains unchanged because

$$\sum_i \mathsf{pk}'_i = \sum_i \mathsf{pk}_i + \sum_i A(\delta_i) = \mathsf{pk} + A\left(\sum_i \delta_i\right) = \mathsf{pk} + A(0) = \mathsf{pk}$$

### Refresh Protocol

A full refresh protocol runs as follows.

1. Each party generates its mask contribution.
2. Parties exchange commitments to their contributions.
3. Parties reveal their contributions.
4. Each party verifies all commitments.
5. Each party computes its new share.
6. Parties publish new commitments to their public shares.
7. External verifiers can check the consistency of the new public shares.

### Public Key Invariance Theorem

```lean
lemma refresh_pk_unchanged
  (S : Scheme)
  (m : MaskFn S)
  (shares : List (KeyShare S))
  (hsum : (shares.map (fun ks => m.mask ks.pid)).sum = 0) :
  let refreshed := refreshShares S m shares
  (refreshed.foldl (fun acc ks => acc + ks.pk_i) (0 : S.Public)) =
  (shares.foldl (fun acc ks => acc + ks.pk_i) (0 : S.Public))
```

If the mask sums to zero over the participant list, the global pk is unchanged.

### Refresh State (CRDT)

```lean
structure RefreshState (S : Scheme) :=
  (mask : MaskFn S)

instance (S : Scheme) : Join (RefreshState S)
instance (S : Scheme) : SemilatticeSup (RefreshState S)
```

### Security Properties

**Forward secrecy.** Old shares reveal nothing about new shares.

**Backward secrecy.** New shares reveal nothing about old shares.

**Invariant preservation.** The master secret and global public key are unchanged.

## Share Repair

Share repair allows a party to recover a lost share. The recovering party receives help from other parties.

### Repair Request Structure

```lean
structure RepairRequest (S : Scheme) :=
  (requester : S.PartyId)
  (knownPk_i : S.Public)  -- The public share is still known

structure RepairMsg (S : Scheme) :=
  (from   : S.PartyId)
  (to     : S.PartyId)
  (delta  : S.Secret)

structure RepairBundle (S : Scheme) :=
  (msgs : List (RepairMsg S))

instance (S : Scheme) : Join (RepairBundle S) := ⟨fun a b => ⟨a.msgs ++ b.msgs⟩⟩
```

Repair bundles merge via list append.

### Repair Session State

The repair session tracks protocol progress with CRDT merge semantics.

```lean
structure RepairSession (S : Scheme) :=
  (request   : RepairRequest S)
  (helpers   : Finset S.PartyId)
  (received  : RepairBundle S)
  (threshold : Nat)

instance (S : Scheme) : Join (RepairSession S)
```

### Repair Scenario

Party $P_i$ has lost its share $s_i$. It wants to recover the share without other parties learning it.

### Helper Protocol

Each helper $P_j$ sends a masked delta to $P_i$. The deltas are structured so that their sum equals $s_i$.

Let $\Delta_{ji}$ denote the message from $P_j$ to $P_i$. The messages satisfy

$$\sum_{j \neq i} \Delta_{ji} = s_i$$

### Repair Function

```lean
def repairShare
  (S : Scheme)
  (msgs : List (RepairMsg S))
  : S.Secret :=
  msgs.foldl (fun acc m => acc + m.delta) (0 : S.Secret)
```

### Correctness

```lean
lemma repair_correct
  (S : Scheme)
  (msgs : List (RepairMsg S))
  (sk_i : S.Secret)
  (h : msgs.foldl (fun acc m => acc + m.delta) (0 : S.Secret) = sk_i) :
  repairShare S msgs = sk_i
```

### Privacy (Zero-Sum Masks)

Additional zero-sum masks do not change the repaired value:

```lean
lemma repair_masked_zero
  (S : Scheme)
  (msgs : List (RepairMsg S))
  (mask : List S.Secret)
  (hmask : mask.sum = 0)
  (hlen : mask.length = msgs.length) :
  repairShare S (List.zipWith (fun m z => { m with delta := m.delta + z }) msgs mask)
    = repairShare S msgs
```

### Construction

One construction uses Lagrange interpolation. If the shares are polynomial shares evaluated at distinct points then any $t$ parties can reconstruct the share at any point.

For additive shares a simpler approach works. Each helper $P_j$ sends a random share of its own share $s_j$. The recovering party combines these to reconstruct its share through a pre-established linear relation.

### Helper Contribution Function

```lean
def helperContribution
  (S : Scheme)
  (helper : KeyShare S)
  (requester : S.PartyId)
  (coefficient : S.Scalar)
  : RepairMsg S :=
  { from  := helper.pid
  , to    := requester
  , delta := coefficient • helper.sk_i }
```

### Verification

```lean
def verifyRepairedShare
  (S : Scheme)
  (repairedSk : S.Secret)
  (expectedPk : S.Public)
  : Prop :=
  S.A repairedSk = expectedPk
```

### Threshold Completion

```lean
def hasEnoughHelpers
  (S : Scheme) [DecidableEq S.PartyId]
  (session : RepairSession S)
  : Bool :=
  (helperPids S session.received.msgs).length ≥ session.threshold

def tryCompleteRepair
  (S : Scheme) [DecidableEq S.PartyId]
  (session : RepairSession S)
  : Option S.Secret
```

### Security

**Privacy.** No single helper learns $s_i$. Zero-sum masking ensures that additional randomness does not affect the reconstructed value.

**Correctness.** The recovered share equals the original share. Verified via `verifyRepairedShare`.

**Threshold.** At least $t$ helpers must participate. Enforced by `hasEnoughHelpers`.

**Robustness.** If threshold is met, `tryCompleteRepair` returns `Some`.

### Repair Protocol Steps

1. Party $P_i$ broadcasts a `RepairRequest` with its known public share.
2. Each helper $P_j$ computes its delta via `helperContribution`.
3. Each helper sends the `RepairMsg` to $P_i$ over a secure channel.
4. Party $P_i$ collects messages in a `RepairSession` (CRDT-mergeable).
5. When `hasEnoughHelpers` returns true, party $P_i$ calls `tryCompleteRepair`.
6. Party $P_i$ verifies $A(s_i) = \mathsf{pk}_i$ via `verifyRepairedShare`.

## Rerandomization

Rerandomization adds privacy by masking shares and nonces. It prevents linking between signing sessions.

### Rerandomization Masks Structure

```lean
structure RerandMasks (S : Scheme) :=
  (shareMask : S.PartyId → S.Secret)
  (nonceMask : S.PartyId → S.Secret)
  (shareSumZero : ∀ (Sset : List S.PartyId), (Sset.map shareMask).sum = 0)
  (nonceSumZero : ∀ (Sset : List S.PartyId), (Sset.map nonceMask).sum = 0)

instance (S : Scheme) : Join (RerandMasks S)
```

Masks merge by pointwise addition. Zero-sum is preserved by additivity.

### Motivation

Without rerandomization the same shares produce related signatures. An observer might link signatures to the same key or signer set. Rerandomization breaks this linkage.

### State Rerandomization

```lean
def rerandState
  (S : Scheme)
  (masks : RerandMasks S)
  (st : SignLocalState S) : SignLocalState S :=
{ st with
  y_i := st.y_i + masks.nonceMask st.share.pid,
  w_i := S.A (st.y_i + masks.nonceMask st.share.pid),
  share := { st.share with
    sk_i := st.share.sk_i + masks.shareMask st.share.pid,
    pk_i := S.A (st.share.sk_i + masks.shareMask st.share.pid) } }
```

### Share Rerandomization

Before signing each party adds a mask to its share.

$$s'_i = s_i + \delta_i$$

The masks must sum to zero as in refresh. The signing protocol uses the masked shares. The verification equation remains valid because the master secret is unchanged.

### Nonce Rerandomization

Similarly parties can add masks to their nonces.

$$y'_i = y_i + \gamma_i$$

If $\sum_i \gamma_i = 0$ then the aggregated nonce is unchanged.

$$w = \sum_i A(y'_i) = \sum_i A(y_i) + A\left(\sum_i \gamma_i\right) = \sum_i A(y_i) + 0$$

### Signature Preservation Theorem

```lean
lemma rerand_preserves_sig
  (S : Scheme)
  (masks : RerandMasks S)
  (Sset : List S.PartyId)
  (c : S.Challenge)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S)) :
  (shares.map (fun sh => masks.shareMask sh.from)).sum = 0 →
  aggregateSignature S c Sset commits
    (shares.map (fun sh => { sh with z_i := sh.z_i + masks.shareMask sh.from }))
    = aggregateSignature S c Sset commits shares
```

### Combined Rerandomization

A full rerandomization applies masks to both shares and nonces. The masks must satisfy the zero-sum property independently.

$$\sum_i \delta_i = 0$$
$$\sum_i \gamma_i = 0$$

### Unlinkability

Rerandomization provides unlinkability. An adversary who sees multiple signatures cannot determine if they were produced by the same set of parties. Each session appears independent.

### Protocol Integration

Rerandomization integrates into the signing protocol as follows.

1. Before round one parties agree on a session identifier.
2. Each party derives its masks from the session identifier and randomness.
3. Parties exchange commitments to their masked values.
4. The signing protocol proceeds with masked shares and nonces.
5. The final signature is identical to one produced without rerandomization.

## Party Addition and Removal

The protocol can add or remove parties from the signer set.

### Party Removal

To remove party $P_k$ the remaining parties redistribute its share. This is equivalent to a repair followed by a refresh. The share $s_k$ is recovered and then split among the remaining parties.

### Party Addition

To add party $P_{n+1}$ the existing parties run a refresh that creates a new share. The new share $s_{n+1}$ is generated such that the shares still sum to the master secret.

### Threshold Adjustment

Changing the threshold requires restructuring the shares. Moving from $t$-of-$n$ to $t'$-of-$n$ requires a new secret sharing polynomial of degree $t'-1$. This is more complex than simple refresh.

## Key Rotation

Key rotation changes the master secret and public key. Unlike refresh which preserves the key rotation generates a new key.

### Rotation Procedure

1. Parties run a new DKG protocol.
2. The new protocol produces fresh shares $s'_i$ for a new secret $s'$.
3. The new public key is $\mathsf{pk}' = A(s')$.
4. External systems update to use the new public key.

### Migration

Applications must migrate from the old key to the new key. Signatures under the old key remain valid. New signatures use the new key.

## Composite State (CRDT)

Protocol phase state combines with refresh, repair, and rerandomization state in a product semilattice.

```lean
abbrev CompositeState (S : Scheme) (p : Phase) :=
  (State S p) × RefreshState S × RepairBundle S × RerandMasks S
```

Merge is provided by the product semilattice instances. This allows all extension state to be merged atomically with protocol progress.

## Threshold-Aware Merge

For threshold protocols, the `ShareWithCtx` structure couples share state with threshold context.

```lean
def mergeShareWithCtx (S : Scheme) [DecidableEq S.PartyId]
  (a b : ShareWithCtx S) : ShareWithCtx S :=
  let mergedActive := a.state.active ∪ b.state.active
  let state := { commits := a.state.commits ⊔ b.state.commits,
                 reveals := a.state.reveals ⊔ b.state.reveals,
                 shares  := a.state.shares ⊔ b.state.shares,
                 active  := mergedActive }
  let t := Nat.max a.ctx.t b.ctx.t
  have hcard : t ≤ mergedActive.card := ...
  let ctx := { active := mergedActive, t := t, card_ge := hcard }
  { state := state, ctx := ctx }
```

The merge:
- Unions the active participant sets
- Takes the maximum threshold
- Proves the merged active set satisfies the threshold requirement
