/-
# DKG Types

Core type definitions for Distributed Key Generation.
Split from Core/Core.lean for better organization.

See DKG/Core.lean for the full protocol implementation.
-/

import IceNine.Protocol.Core.Core

namespace IceNine.Protocol

/-!
## Proof of Knowledge (FROST Pattern)

Following FROST, DKG includes a proof of knowledge (PoK) to prevent rogue-key attacks.
Without PoK, an adversary could choose their public key as a function of honest parties'
keys, potentially biasing the aggregate key.

The PoK is a Schnorr-style proof: given pk_i = A(sk_i), prove knowledge of sk_i.
1. Prover samples random k, computes R = A(k)
2. Challenge c = H_dkg(pid, pk_i, R)
3. Response μ = k + c·sk_i
4. Verifier checks: A(μ) = R + c·pk_i

**Security**: This prevents rogue-key attacks because the adversary must know sk_i
to produce a valid proof. They cannot adaptively choose pk_i after seeing others' keys.

Reference: FROST RFC Section 5.1, Komlo & Goldberg "FROST" (2020)
-/

/-- Proof of knowledge for DKG: proves knowledge of secret corresponding to public key.
    Schnorr-style: given pk = A(sk), prove knowledge of sk. -/
structure ProofOfKnowledge (S : Scheme) where
  /-- Commitment R = A(k) for random nonce k -/
  commitment : S.Public
  /-- Response μ = k + c·sk where c = H_dkg(pid, pk, R) -/
  response   : S.Secret

/-- DKG round 1: party broadcasts commitment to its public share.
    Hiding pk_i until all parties commit prevents adaptive attacks.
    Includes proof of knowledge to prevent rogue-key attacks. -/
structure DkgCommitMsg (S : Scheme) where
  sender   : S.PartyId
  commitPk : S.Commitment
  /-- Proof of knowledge of secret corresponding to public share -/
  pok      : ProofOfKnowledge S


/-- DKG round 2: party reveals pk_i and opening to verify commitment.
    Others check: commit(pk_i, opening) = commitPk from round 1. -/
structure DkgRevealMsg (S : Scheme) where
  sender  : S.PartyId
  pk_i    : S.Public
  opening : S.Opening


/-- Party's local state during DKG. The secret sk_i is sampled locally
    and never transmitted. Only the commitment/reveal are broadcast. -/
structure DkgLocalState (S : Scheme) where
  pid    : S.PartyId
  sk_i   : S.Secret     -- locally sampled secret share
  pk_i   : S.Public     -- pk_i = A(sk_i)
  openPk : S.Opening    -- randomness for commitment

end IceNine.Protocol
