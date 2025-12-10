/-
# Signing correctness and validation lemmas
-/

import IceNine.Protocol.Sign

namespace IceNine.Security.Sign

open IceNine.Protocol
open List

lemma aggregateSignatureLagrangeThresh_sound
  (S    : Scheme)
  (c    : S.Challenge)
  (ctx  : ThresholdCtx S)
  (commits : List S.Commitment)
  (coeffs : List (LagrangeCoeff S))
  (shares : List (SignShareMsg S))
  (hfrom : sharesFromActive S ctx shares) :
  (aggregateSignatureLagrangeThresh S c ctx commits coeffs shares).Sset = ctx.active.toList := by
  simp [aggregateSignatureLagrangeThresh]

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

lemma validateSigning_duplicate
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  (hlen : commits.length = reveals.length ∧ reveals.length = shares.length)
  (hdup : ¬ (commits.map (·.from)).Nodup) :
  validateSigning S pk m Sset commits reveals shares = Except.error (.duplicateParticipants (commits.headD (by cases commits <;> simp))) := by
  unfold validateSigning; simp [hlen, hdup]

lemma validateSigning_participantMismatch
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  (hlen : commits.length = reveals.length ∧ reveals.length = shares.length)
  (hdup : (commits.map (·.from)).Nodup)
  (hpids : commits.map (·.from) ≠ Sset) :
  validateSigning S pk m Sset commits reveals shares = Except.error (.participantMismatch (commits.headD (by cases commits <;> simp))) := by
  unfold validateSigning; simp [hlen, hdup, hpids]

lemma validateSigning_commitMismatch
  (S     : Scheme) [DecidableEq S.PartyId]
  (pk    : S.Public)
  (m     : S.Message)
  (Sset  : List S.PartyId)
  (commits : List (SignCommitMsg S))
  (reveals : List (SignRevealWMsg S))
  (shares  : List (SignShareMsg S))
  (hlen : commits.length = reveals.length ∧ reveals.length = shares.length)
  (hdup : (commits.map (·.from)).Nodup)
  (hpids : commits.map (·.from) = Sset)
  (hexists : ∃ (c r), (c,r) ∈ List.zip commits reveals ∧ S.commit r.w_i r.opening ≠ c.commitW) :
  ∃ pid, validateSigning S pk m Sset commits reveals shares = Except.error (.commitMismatch pid) := by
  unfold validateSigning
  simp [hlen, hdup, hpids]
  rcases hexists with ⟨c,r,hzr,hm⟩
  exact ⟨r.from, by simp [hm, hzr]⟩

lemma aggregateSignature_add_masks
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  (mask : S.PartyId → S.Secret) :
  let shares' := shares.map (fun sh => { sh with z_i := sh.z_i + mask sh.from })
  (aggregateSignature S c Sset commits shares').z
    = (aggregateSignature S c Sset commits shares).z
      + (shares.map (fun sh => mask sh.from)).sum := by
  unfold aggregateSignature
  simp [List.map_map, List.foldl_map, add_comm, add_left_comm, add_assoc, List.map, Function.comp]

lemma aggregateSignature_masks_zero
  (S    : Scheme)
  (c    : S.Challenge)
  (Sset : List S.PartyId)
  (commits : List S.Commitment)
  (shares : List (SignShareMsg S))
  (mask : S.PartyId → S.Secret)
  (hzero : (shares.map (fun sh => mask sh.from)).sum = 0) :
  aggregateSignature S c Sset commits (shares.map (fun sh => { sh with z_i := sh.z_i + mask sh.from }))
  = aggregateSignature S c Sset commits shares := by
  ext <;> simp [aggregateSignature_add_masks, hzero, aggregateSignature]

end IceNine.Security.Sign
