/-
# Trusted-dealer key generation (lattice, additive shares)
-/

import IceNine.Protocol.Core
import IceNine.Protocol.DKGCore

namespace IceNine.Protocol

open List

/-- Dealer output: participant share plus public commitment. -/
structure DealerShare (S : Scheme) :=
  (pid    : S.PartyId)
  (sk_i   : S.Secret)
  (pk_i   : S.Public)
  (opening : S.Opening)
  (commitPk : S.Commitment)

/-- Dealer transcript: all shares and global pk. -/
structure DealerTranscript (S : Scheme) :=
  (shares : List (DealerShare S))
  (pk     : S.Public)

/--
  Dealer keygen: sample short shares, compute pk_i = A sk_i, commit, and
  aggregate pk = Σ pk_i. Randomness for sk_i/openings is passed in to stay pure.
-/
def dealerKeygen
  (S : Scheme)
  (pids    : List S.PartyId)
  (secrets : List S.Secret)
  (opens   : List S.Opening)
  : Option (DealerTranscript S) :=
  if hlen : pids.length = secrets.length ∧ secrets.length = opens.length then
    let shares :=
      List.zipWith3
        (fun pid sk op =>
          let pk_i := S.A sk
          let com  := S.commit pk_i op
          { pid := pid, sk_i := sk, pk_i := pk_i, opening := op, commitPk := com })
        pids secrets opens
    let pk := shares.foldl (fun acc sh => acc + sh.pk_i) (0 : S.Public)
    some ⟨shares, pk⟩
  else
    none

/-- Dealer correctness: pk is sum of pk_i. -/
lemma dealerKeygen_pk
  (S : Scheme)
  {pids : List S.PartyId} {secrets : List S.Secret} {opens : List S.Opening}
  {tr : DealerTranscript S}
  (h : dealerKeygen S pids secrets opens = some tr) :
  tr.pk = tr.shares.foldl (fun acc sh => acc + sh.pk_i) (0 : S.Public) := by
  unfold dealerKeygen at h
  by_cases hlen : pids.length = secrets.length ∧ secrets.length = opens.length
  · simp [hlen] at h
    cases h with
    | rfl => rfl
  · simp [hlen] at h

/-- Binding: if two dealer transcripts have same commitments, pk_i coincide. -/
lemma dealer_commit_binding
  (S : Scheme)
  {sh1 sh2 : DealerShare S}
  (h : sh1.commitPk = sh2.commitPk) :
  sh1.pk_i = sh2.pk_i := by
  have := S.commitBinding (x₁ := sh1.pk_i) (x₂ := sh2.pk_i) (o₁ := sh1.opening) (o₂ := sh2.opening)
  simpa [DealerShare.commitPk] using this h

end IceNine.Protocol
