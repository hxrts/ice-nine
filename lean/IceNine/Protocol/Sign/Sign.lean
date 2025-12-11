/-
# Threshold Signing Protocol

Two-round threshold signing following the Schnorr pattern:
  Round 1: Parties commit to ephemeral nonces
  Round 2: Parties reveal nonces, compute challenge, produce partial signatures
  Aggregation: Combine partials into final signature

Supports both n-of-n (all parties) and t-of-n (threshold) signing.
Security proofs in `Proofs/Correctness/Sign`.

## Module Structure

This module re-exports from the split submodules for backward compatibility:
- `SignTypes.lean`: Core types (SessionTracker, messages, errors)
- `SignCore.lean`: Challenge computation, n-of-n aggregation
- `SignThreshold.lean`: Coefficient strategies, threshold context

## API

**Use the session-typed API from `IceNine.Protocol.SignSession`.**

The session-typed API provides compile-time guarantees against nonce reuse:
- Each `FreshNonce` can only be consumed once
- Session states progress linearly: ReadyToCommit → Committed → Revealed → Signed → Done
- Retry handling requires a NEW fresh nonce

Example:
```lean
import IceNine.Protocol.Sign.Session
open IceNine.Protocol.SignSession

-- Initialize with fresh nonce
let ready := initSession S keyShare message sessionId y opening
-- Commit (consumes ready, produces committed)
let (committed, commitMsg) := commit S ready
-- ... receive all commits, compute challenge ...
-- Reveal (consumes committed)
let (revealed, revealMsg) := reveal S committed challenge aggregateW
-- Sign (consumes revealed)
match sign S revealed with
| Sum.inl signed => finalize S signed
| Sum.inr (_, reason) => -- retry with FRESH nonce
```

This module provides supporting types, validation, and aggregation functions.
The raw `signRound1` and `signRound2` functions have been removed to prevent
accidental nonce misuse.

## Session and Nonce Safety

**CRITICAL**: Nonce reuse is catastrophic for Schnorr-style signatures.
If the same nonce y is used with two different challenges c₁, c₂:
  z₁ = y + c₁·sk
  z₂ = y + c₂·sk
Then: sk = (z₁ - z₂) / (c₁ - c₂)  -- secret key recovered!

We track used sessions to prevent this attack vector.

### Session ID Generation

Session IDs must be unique across all signing sessions for a given party.
Recommended strategies (in order of preference):

1. **Cryptographic random**: Generate 128+ bit random session ID using CSPRNG.
   Collision probability negligible. Best for distributed systems.

2. **Monotonic counter + party ID**: `(partyId, counter)` tuple where counter
   increments locally. Requires persistent storage but deterministic.

3. **Timestamp + random**: `(timestamp_ns, random_64bit)`. Good balance of
   uniqueness and debuggability.

**WARNING**: Do NOT use:
- Sequential counters without party ID (collisions across parties)
- Predictable values (may enable targeted attacks)
- Message hash alone (same message = same session = nonce reuse!)

The `SessionTracker` provides runtime detection of session reuse,
but proper generation is the primary defense.
-/

-- Re-export from split modules for backward compatibility
import IceNine.Protocol.Sign.Types
import IceNine.Protocol.Sign.Core
import IceNine.Protocol.Sign.Threshold

/-!
All types and functions from SignTypes, SignCore, and SignThreshold are
available through this module for backward compatibility:

## From SignTypes
- `SessionTracker`, `NonceRegistry` - session/nonce tracking
- `SignLocalState`, `SignCommitMsg`, `SignRevealWMsg` - state and messages
- `LagrangeCoeff` - coefficient structure
- `SignError`, `AbortReason`, `SignAbortMsg`, `SignAbortState` - error handling
- `Signature`, `SignatureDone`, `DoneState` - output types

## From SignCore
- `lagrangeCoeffAtZero`, `lagrangeCoeffs` - Lagrange computation
- `computeChallenge` - Fiat-Shamir challenge
- `aggregateSignature`, `aggregateSignatureLagrange` - aggregation
- `ValidSignTranscript`, `validateSigning` - validation

## From SignThreshold
- `CoeffStrategy`, `strategyOK` - aggregation strategy
- `SignMode`, `ThresholdCtx` - threshold context
- `mkAllCtx`, `mkThresholdCtx`, `mkThresholdCtxComputed` - constructors
- `aggregateWithStrategy`, `aggregateSignatureWithCtx` - context-based aggregation
-/
