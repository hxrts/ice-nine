/-
# Signing Security Proofs

Validation lemmas and mask invariants for the signing protocol:
- Error conditions: characterize when validateSigning returns each error
- Mask invariance: zero-sum masks don't change aggregated signature
- Threshold soundness: shares from active set produce correct Sset

NOTE: Many lemmas are currently stubbed with `sorry` due to API changes in the
signing protocol (validateSigning now requires BindingFactors parameter).
These will be updated once the binding factor infrastructure is stabilized.
-/

import IceNine.Protocol.Sign.Types
import IceNine.Protocol.Sign.Core
import IceNine.Protocol.Sign.Threshold

namespace IceNine.Proofs.Correctness.Sign

open IceNine.Protocol
open List

/-!
## Threshold Aggregation Soundness

Threshold aggregation preserves the signer set.
-/

/-- Threshold aggregation produces signature with correct Sset. -/
lemma aggregateSignatureLagrangeThresh_sound
  (S    : Scheme) [DecidableEq S.PartyId]
  (c    : S.Challenge)
  (ctx  : ThresholdCtx S)
  (commits : List S.Commitment)
  (coeffs : List (LagrangeCoeff S))
  (shares : List (SignShareMsg S))
  (_hfrom : sharesFromActive S ctx shares) :
  (aggregateSignatureLagrangeThresh S c ctx commits coeffs shares).Sset = ctx.active.toList := by
  simp only [aggregateSignatureLagrangeThresh, aggregateSignatureLagrange]

/-!
## Error Characterization

NOTE: The following lemmas are commented out because validateSigning now requires
a BindingFactors parameter. They will be updated once the binding factor API is stable.

Each error from validateSigning has a corresponding lemma characterizing
the preconditions that cause it:
- validateSigning_lengthMismatch
- validateSigning_duplicate
- validateSigning_participantMismatch
- validateSigning_commitMismatch
-/

-- Error characterization lemmas stubbed - API changed to require BindingFactors

/-!
## Mask Invariance

Zero-sum masks don't change the aggregated signature.
Key for rerandomization security.
-/

/-- Masks add to z: masked shares aggregate to z + Σmasks. -/
lemma aggregateSignature_add_masks
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  (mask : S.PartyId → S.Secret) :
  let shares' := shares.map (fun sh => { sh with z_i := sh.z_i + mask sh.sender })
  (aggregateSignature S c Sset commits shares').z
    = (aggregateSignature S c Sset commits shares).z
      + (shares.map (fun sh => mask sh.sender)).sum := by
  unfold aggregateSignature
  -- Proof requires showing sum distributes over the mapped transformation
  sorry

/-- Zero-sum masks: if Σ mask(i) = 0, masked aggregate = original.
    This is the key property for rerandomization privacy. -/
lemma aggregateSignature_masks_zero
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  (mask : S.PartyId → S.Secret)
  (_hzero : (shares.map (fun sh => mask sh.sender)).sum = 0) :
  aggregateSignature S c Sset commits (shares.map (fun sh => { sh with z_i := sh.z_i + mask sh.sender }))
  = aggregateSignature S c Sset commits shares := by
  -- Requires Signature extensionality and aggregateSignature_add_masks
  sorry

/-!
## CRDT pipeline to verification (all-ones strategy)

NOTE: These lemmas depend on `ShareWithCtx` (from ThresholdMerge) and `verify`
(signature verification function) which are not yet wired up. The proofs are
commented out until the full verification pipeline is implemented.
-/

-- The following lemmas require ShareWithCtx from ThresholdMerge and a verify function.
-- They will be uncommented once the verification infrastructure is complete.

-- lemma tryAggregate_verify_ones : proof depends on ShareWithCtx, verify
-- lemma tryAggregate_verify_lagrange : proof depends on ShareWithCtx, verify

/-!
## Nonce Reuse Attack

**CRITICAL SECURITY PROPERTY**: Nonce reuse completely breaks Schnorr signatures.

If the same nonce y is used with two different challenges c₁ ≠ c₂:
  z₁ = y + c₁·sk
  z₂ = y + c₂·sk

Then the secret key can be recovered:
  z₁ - z₂ = (c₁ - c₂)·sk
  sk = (z₁ - z₂) / (c₁ - c₂)

This section formalizes the attack and proves that fresh sessions prevent it.
-/

/-- The nonce reuse attack: given two signatures with same nonce, recover secret.
    This demonstrates WHY nonce freshness is critical. -/
structure NonceReuseAttack (S : Scheme) [Field S.Scalar]
    [HSMul S.Challenge S.Secret S.Secret] where
  /-- The reused nonce -/
  y : S.Secret
  /-- First challenge -/
  c1 : S.Challenge
  /-- Second challenge (must differ from c1) -/
  c2 : S.Challenge
  /-- First response z₁ = y + c₁·sk -/
  z1 : S.Secret
  /-- Second response z₂ = y + c₂·sk -/
  z2 : S.Secret
  /-- Challenges are different -/
  challenges_differ : c1 ≠ c2

/-- Key recovery from nonce reuse (conceptual - requires division in Secret space).

    In practice: if Secret = Scalar (field elements), this directly computes sk.
    For lattice schemes: the difference z₁ - z₂ = (c₁ - c₂)·sk leaks information
    about sk, which can be exploited with enough samples. -/
def recoverSecretFromReuseSimple
    (z1 z2 : Int) (c1 c2 : Int) (_hne : c1 ≠ c2) : Int :=
  (z1 - z2) / (c1 - c2)

/-- Session freshness implies nonce safety.
    If session IDs are unique and nonces are deterministically derived from
    (secret randomness, session ID), then nonces are unique. -/
lemma fresh_session_unique_nonce
    (S : Scheme)
    (tracker : SessionTracker S)
    (s1 s2 : Nat)
    (_h1 : tracker.isFresh s1)
    (_h2 : tracker.isFresh s2)
    (hne : s1 ≠ s2)
    -- Assume nonces are deterministic functions of session + secret seed
    (nonceFromSession : Nat → S.Secret)
    (hInj : Function.Injective nonceFromSession) :
    nonceFromSession s1 ≠ nonceFromSession s2 := by
  exact fun h => hne (hInj h)

/-- Tracking prevents reuse: after marking session used, it's no longer fresh -/
lemma markUsed_not_fresh
    (S : Scheme)
    (tracker : SessionTracker S)
    (session : Nat) :
    ¬ (tracker.markUsed session).isFresh session := by
  simp [SessionTracker.markUsed, SessionTracker.isFresh, Finset.mem_insert]

/-- A session that was never used is always fresh -/
lemma empty_tracker_all_fresh
    (S : Scheme) (pid : S.PartyId) (session : Nat) :
    (SessionTracker.empty S pid).isFresh session := by
  simp [SessionTracker.empty, SessionTracker.isFresh]

end IceNine.Proofs.Correctness.Sign
