/-
# Trusted dealer keygen

Dealer-supplied shares and commitments. Proofs live in `Security/DKG`.
-/

import IceNine.Protocol.DKGCore

namespace IceNine.Protocol

structure DealerShare (S : Scheme) :=
  (pid    : S.PartyId)
  (sk_i   : S.Secret)
  (pk_i   : S.Public)
  (opening : S.Opening)
  (commitPk : S.Commitment)

structure DealerTranscript (S : Scheme) :=
  (shares : List (DealerShare S))
  (pk     : S.Public)

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

end IceNine.Protocol
