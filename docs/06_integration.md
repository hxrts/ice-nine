# Protocol Integration

Ice Nine provides integration points for external consensus and coordination protocols. This document describes how to integrate Ice Nine's threshold signing with protocols like Aura.

## External Context

External protocols can attach context to signing messages using the `ExternalContext` structure. This enables binding signatures to consensus instances without coupling Ice Nine to specific protocols.

```lean
structure ExternalContext where
  consensusId : Option ByteArray := none    -- external session identifier
  resultId : Option ByteArray := none       -- what is being signed (e.g., H(op, prestate))
  prestateHash : Option ByteArray := none   -- state validation
  evidenceDelta : Option ByteArray := none  -- CRDT evidence for propagation
```

### Usage Pattern

1. **Attach context when creating messages**:
   ```lean
   let ctx : ExternalContext := {
     consensusId := some myConsensusId
     resultId := some (hashOf operation prestate)
     prestateHash := some prestateHash
   }
   let share : SignShareMsg S := { sender := pid, session := sess, z_i := z, context := ctx }
   ```

2. **Validate context consistency during aggregation**:
   ```lean
   match aggregateWithContextValidation S c signers commits shares with
   | .ok signature => -- all shares reference same consensus instance
   | .error msg => -- inconsistent context detected
   ```

3. **Access context from signatures**:
   ```lean
   let sig := aggregateSignature S c signers commits shares
   let consensusId := sig.context.consensusId
   ```

## Evidence Carrier

The `EvidenceCarrier` typeclass enables piggybacking CRDT evidence deltas on signing messages. This is useful for protocols like Aura that propagate evidence alongside consensus messages.

```lean
class EvidenceCarrier (M : Type*) where
  attachEvidence : M → ByteArray → M
  extractEvidence : M → Option ByteArray
  hasEvidence : M → Bool
```

### Instances

All signing message types implement `EvidenceCarrier`:
- `SignCommitMsg`
- `SignRevealWMsg`
- `SignShareMsg`
- `Signature`
- `ValidatableShare`

### Usage

```lean
-- Attach evidence before sending
let msgWithEvid := EvidenceCarrier.attachEvidence msg myEvidenceDelta

-- Extract evidence on receive
match EvidenceCarrier.extractEvidence msg with
| some delta => mergeEvidence delta
| none => ()
```

## Fast Path Signing

For low-latency consensus, Ice Nine supports precomputed nonces that enable single-round signing.

### Precomputed Nonces

Parties can pre-generate nonces during idle time:

```lean
-- Generate during idle time
let precomputed := PrecomputedNonce.create S hiding binding opening currentTime

-- Pre-share the commitment
let preshared := PreSharedCommitment.fromPrecomputed S partyId precomputed
broadcast preshared

-- When signing request arrives, produce share immediately
match signFast S keyShare precomputed challenge bindingFactor session context with
| some share => send share
| none => -- norm check failed, need fresh nonce
```

### Nonce Pool Management

For concurrent signing sessions, use `NoncePool`:

```lean
-- Initialize pool
let pool := NoncePool.empty S

-- Add precomputed nonces during idle
let pool := pool.add precomputed1
let pool := pool.add precomputed2

-- Take nonce for signing (automatically prunes expired)
match pool.take currentTime with
| some (nonce, pool') => use nonce, update pool to pool'
| none => generate fresh nonce
```

### Security Assumptions

Fast path signing trusts that:
1. Nonce commitments were honestly generated
2. Nonces are not being reused
3. Precomputed nonces have not expired
4. Coordinator will aggregate honestly

Use standard two-round signing when these assumptions don't hold.

## Self-Validating Shares

For fallback gossip protocols, `ValidatableShare` bundles a share with enough context for independent validation:

```lean
structure ValidatableShare (S : Scheme) where
  share : SignShareMsg S
  nonceCommit : S.Commitment
  publicHiding : S.Public
  publicBinding : S.Public
  pkShare : S.Public
```

### Creating ValidatableShares

```lean
let vs := ValidatableShare.create S shareMsg commitMsg partyPublicKey
```

### Use Case: Aura Fallback

In Aura's fallback protocol, witnesses gossip shares to achieve threshold:

```lean
-- Create self-validating share for gossip
let validatable := ValidatableShare.create S myShare myCommit myPkShare

-- Recipients can validate without full session state
if validatable.isWellFormed then
  addToProposals validatable
```

## Aura Integration Example

Here's how Ice Nine maps to Aura's fast path:

### Setup Phase

1. **DKG**: Use Ice Nine's DKG to establish shared threshold key material
2. **Pre-share commitments**: Witnesses periodically broadcast `PreSharedCommitment` values

### Fast Path

1. **Execute**: Initiator sends `Execute(cid, Op, prestate_hash, evidΔ)`

2. **Witness Share Production**:
   ```lean
   -- Compute result ID
   let rid := hash operation prestate

   -- Create context
   let ctx : ExternalContext := {
     consensusId := some cid
     resultId := some rid
     prestateHash := some prestateHash
     evidenceDelta := some evidDelta
   }

   -- Produce share using precomputed nonce
   let share := signFast S keyShare precomputed challenge bindingFactor session ctx
   ```

3. **Aggregation**:
   ```lean
   -- Validate all shares reference same consensus instance
   match aggregateWithContextValidation S challenge signers commits shares with
   | .ok signature =>
       -- Extract merged context for CommitFact
       let thresholdSig := signature
       let attesters := signature.Sset
       commitFact cid rid thresholdSig attesters
   | .error msg =>
       -- Inconsistent shares, enter fallback
       startFallback msg
   ```

### Fallback

Use `ValidatableShare` for gossip:

```lean
-- Wrap shares for independent validation
let proposal := ValidatableShare.create S share commit pkShare

-- Gossip to peers
for peer in randomSubset witnesses k do
  send (AggregateShare cid proposals evidDelta) peer

-- On receive, validate and accumulate
for vs in received do
  if vs.isWellFormed && !hasEquivocated vs.sender then
    addProposal vs
    if proposalCount rid >= threshold then
      produceThresholdSignature rid proposals
```

## Context Validation

When aggregating shares from multiple parties, validate context consistency:

```lean
def validateShareContexts (shares : List (SignShareMsg S)) : ContextValidationResult

-- Returns:
-- - .ok : all contexts consistent
-- - .inconsistentConsensusId i j : shares i,j have different cid
-- - .inconsistentResultId i j : shares i,j have different rid
-- - .inconsistentPrestateHash i j : shares i,j have different prestate
```

This catches Byzantine behavior where a party signs different operations.

## Best Practices

1. **Always set consensusId**: Bind shares to specific consensus instances
2. **Include resultId**: Ensures all parties sign the same computed result
3. **Use precomputed nonces for latency**: But regenerate periodically (default: 1 hour)
4. **Validate context on aggregation**: Detect Byzantine behavior early
5. **Use ValidatableShare for gossip**: Enables independent validation in fallback
6. **Propagate evidence**: Use EvidenceCarrier for CRDT convergence
