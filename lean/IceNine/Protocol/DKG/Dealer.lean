/-
# Trusted Dealer Key Generation

Alternative to DKG: a trusted dealer generates all shares and distributes
them to parties. Simpler but requires trust in the dealer. Useful for
bootstrapping or when a trusted setup is acceptable.
Security proofs in `Security/DKG`.
-/

import IceNine.Protocol.DKG.Core

namespace IceNine.Protocol

/-!
## Dealer Output Types

The dealer produces a share for each party plus the global public key.
Each share includes the secret, public share, and commitment data.
-/

/-- Everything a party receives from the dealer.
    Includes commitment so others can verify consistency. -/
structure DealerShare (S : Scheme) where
  pid      : S.PartyId     -- recipient party ID
  sk_i     : S.Secret      -- secret share (sent privately)
  pk_i     : S.Public      -- public share = A(sk_i)
  opening  : S.Opening     -- commitment randomness
  commitPk : S.Commitment  -- commitment to pk_i

/-- Complete dealer output: all shares plus global public key. -/
structure DealerTranscript (S : Scheme) where
  shares : List (DealerShare S)  -- one per party
  pk     : S.Public              -- global key = Σ pk_i

/-!
## Dealer Key Generation

Dealer receives pre-sampled secrets and produces shares for all parties.
The function is pure: randomness (secrets, openings) is sampled externally.
-/

/-- Generate shares for all parties from pre-sampled secrets.
    Returns None if input lists have mismatched lengths. -/
def dealerKeygen
  (S : Scheme)
  (pids    : List S.PartyId)  -- party identifiers
  (secrets : List S.Secret)   -- pre-sampled secret shares (Σ sk_i = master secret)
  (opens   : List S.Opening)  -- commitment randomness per party
  : Option (DealerTranscript S) :=
  -- Validate all lists have same length
  if hlen : pids.length = secrets.length ∧ secrets.length = opens.length then
    -- Create share for each party
    let shares :=
      List.zipWith3
        (fun pid sk op =>
          -- Compute public share from secret
          let pk_i := S.A sk
          -- Commit to public share for verification
          let com  := S.commit pk_i op
          { pid := pid, sk_i := sk, pk_i := pk_i, opening := op, commitPk := com })
        pids secrets opens
    -- Global public key is sum of all public shares
    let pk := (shares.map (·.pk_i)).sum
    some ⟨shares, pk⟩
  else
    none

end IceNine.Protocol
