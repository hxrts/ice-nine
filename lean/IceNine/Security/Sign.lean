/-
# Signing Security Proofs

Validation lemmas and mask invariants for the signing protocol:
- Error conditions: characterize when validateSigning returns each error
- Mask invariance: zero-sum masks don't change aggregated signature
- Threshold soundness: shares from active set produce correct Sset
-/

import IceNine.Protocol.Sign

namespace IceNine.Security.Sign

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
  (hfrom : sharesFromActive S ctx shares) :
  (aggregateSignatureLagrangeThresh S c ctx commits coeffs shares).Sset = ctx.active.toList := by
  simp [aggregateSignatureLagrangeThresh]

/-!
## Error Characterization

Each error from validateSigning has a corresponding lemma
characterizing the preconditions that cause it.
-/

/-- Length mismatch: commits/reveals/shares counts don't match. -/
lemma validateSigning_lengthMismatch
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  (h : ¬ (commits.length = reveals.length ∧ reveals.length = shares.length)) :
  validateSigning S pk m Sset commits reveals shares = Except.error (.lengthMismatch) := by
  unfold validateSigning; simp [h]

/-- Duplicate error: same party appears twice in commits. -/
lemma validateSigning_duplicate
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  (hlen : commits.length = reveals.length ∧ reveals.length = shares.length)
  (hdup : ¬ (commits.map (·.sender)).Nodup) :
  validateSigning S pk m Sset commits reveals shares = Except.error (.duplicateParticipants (commits.headD (by cases commits <;> simp))) := by
  unfold validateSigning; simp [hlen, hdup]

/-- Participant mismatch: signers don't match expected Sset. -/
lemma validateSigning_participantMismatch
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  (hlen : commits.length = reveals.length ∧ reveals.length = shares.length)
  (hdup : (commits.map (·.sender)).Nodup)
  (hpids : commits.map (·.sender) ≠ Sset) :
  validateSigning S pk m Sset commits reveals shares = Except.error (.participantMismatch (commits.headD (by cases commits <;> simp))) := by
  unfold validateSigning; simp [hlen, hdup, hpids]

/-- Commit mismatch: some reveal doesn't match its commitment. -/
lemma validateSigning_commitMismatch
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  (hlen : commits.length = reveals.length ∧ reveals.length = shares.length)
  (hdup : (commits.map (·.sender)).Nodup)
  (hpids : commits.map (·.sender) = Sset)
  (hexists : ∃ (c r), (c,r) ∈ List.zip commits reveals ∧ S.commit r.w_i r.opening ≠ c.commitW) :
  ∃ pid, validateSigning S pk m Sset commits reveals shares = Except.error (.commitMismatch pid) := by
  unfold validateSigning
  simp [hlen, hdup, hpids]
  rcases hexists with ⟨c,r,hzr,hm⟩
  exact ⟨r.sender, by simp [hm, hzr]⟩

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
  simp only [List.map_map, List.sum_map_add, Function.comp]

/-- Zero-sum masks: if Σ mask(i) = 0, masked aggregate = original.
    This is the key property for rerandomization privacy. -/
lemma aggregateSignature_masks_zero
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  (mask : S.PartyId → S.Secret)
  (hzero : (shares.map (fun sh => mask sh.sender)).sum = 0) :
  aggregateSignature S c Sset commits (shares.map (fun sh => { sh with z_i := sh.z_i + mask sh.sender }))
  = aggregateSignature S c Sset commits shares := by
  ext <;> simp [aggregateSignature_add_masks, hzero, aggregateSignature]

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
    [HSMul : HSMul S.Challenge S.Secret S.Secret] where
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
    (z1 z2 : Int) (c1 c2 : Int) (hne : c1 ≠ c2) : Int :=
  (z1 - z2) / (c1 - c2)

/-- Session freshness implies nonce safety.
    If session IDs are unique and nonces are deterministically derived from
    (secret randomness, session ID), then nonces are unique. -/
lemma fresh_session_unique_nonce
    (tracker : SessionTracker S)
    (s1 s2 : Nat)
    (h1 : tracker.isFresh s1)
    (h2 : tracker.isFresh s2)
    (hne : s1 ≠ s2)
    -- Assume nonces are deterministic functions of session + secret seed
    (nonceFromSession : Nat → S.Secret)
    (hInj : Function.Injective nonceFromSession) :
    nonceFromSession s1 ≠ nonceFromSession s2 := by
  exact fun h => hne (hInj h)

/-- Tracking prevents reuse: after marking session used, it's no longer fresh -/
lemma markUsed_not_fresh
    (tracker : SessionTracker S)
    (session : Nat) :
    ¬ (tracker.markUsed session).isFresh session := by
  simp [SessionTracker.markUsed, SessionTracker.isFresh, Finset.mem_insert]

/-- A session that was never used is always fresh -/
lemma empty_tracker_all_fresh
    (S : Scheme) (pid : S.PartyId) (session : Nat) :
    (SessionTracker.empty S pid).isFresh session := by
  simp [SessionTracker.empty, SessionTracker.isFresh]

end IceNine.Security.Sign
