/-
# Trusted Dealer Key Generation

Alternative to DKG: a trusted dealer generates all shares and distributes
them to parties. Simpler but requires trust in the dealer. Useful for
bootstrapping or when a trusted setup is acceptable.
Security proofs in `Proofs/Correctness/DKG`.
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

/-!
## Dealer Error Types
-/

/-- Errors that can occur during dealer key generation. -/
inductive DealerError
  | lengthMismatch (pids secrets opens : Nat)
      -- Lists have different lengths
  | emptyPartyList
      -- No parties provided
  | duplicateParty (pid : String)
      -- Same party appears twice (requires Repr instance)
  deriving Repr

/-- Convert DealerError to descriptive string. -/
def DealerError.toString : DealerError → String
  | .lengthMismatch p s o =>
      s!"length mismatch: {p} parties, {s} secrets, {o} openings"
  | .emptyPartyList =>
      "empty party list"
  | .duplicateParty pid =>
      s!"duplicate party: {pid}"

instance : ToString DealerError := ⟨DealerError.toString⟩

/-!
## Dealer Key Generation
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
    -- Create share for each party using nested zip
    let shares :=
      (pids.zip (secrets.zip opens)).map fun (pid, sk, op) =>
        -- Compute public share from secret
        let pk_i := S.A sk
        -- Commit to public share for verification
        let com  := S.commit pk_i op
        { pid := pid, sk_i := sk, pk_i := pk_i, opening := op, commitPk := com }
    -- Global public key is sum of all public shares
    let pk := (shares.map (·.pk_i)).sum
    some ⟨shares, pk⟩
  else
    none

/-- Generate shares with detailed error reporting.

    **Effect pattern**: Returns `Except DealerError` for explicit error handling.
    Use this variant when you need diagnostic information.

    Validates:
    - All input lists have matching lengths
    - Party list is non-empty

    For validation with duplicate checking, use `dealerKeygenValidated`. -/
def dealerKeygenE
  (S : Scheme)
  (pids    : List S.PartyId)
  (secrets : List S.Secret)
  (opens   : List S.Opening)
  : Except DealerError (DealerTranscript S) := do
  -- Check non-empty
  if pids.isEmpty then
    throw .emptyPartyList
  -- Check length match
  if pids.length ≠ secrets.length ∨ secrets.length ≠ opens.length then
    throw (.lengthMismatch pids.length secrets.length opens.length)
  -- Generate shares using nested zip
  let shares :=
    (pids.zip (secrets.zip opens)).map fun (pid, sk, op) =>
      let pk_i := S.A sk
      let com  := S.commit pk_i op
      { pid := pid, sk_i := sk, pk_i := pk_i, opening := op, commitPk := com }
  let pk := (shares.map (·.pk_i)).sum
  pure ⟨shares, pk⟩

/-- Generate shares with full validation including duplicate checking.

    **Note**: Requires `DecidableEq` and `Repr` on `PartyId` for duplicate detection
    and error reporting. -/
def dealerKeygenValidated
  (S : Scheme) [DecidableEq S.PartyId] [Repr S.PartyId]
  (pids    : List S.PartyId)
  (secrets : List S.Secret)
  (opens   : List S.Opening)
  : Except DealerError (DealerTranscript S) := do
  -- Check non-empty
  if pids.isEmpty then
    throw .emptyPartyList
  -- Check for duplicates
  let seen := pids.foldl (init := (([] : List S.PartyId), (none : Option S.PartyId))) fun state pid =>
    let (acc, dup) := state
    match dup with
    | some _ => (acc, dup)
    | none => if acc.contains pid then (acc, some pid) else (pid :: acc, none)
  match seen.2 with
  | some dupPid => throw (.duplicateParty (reprStr dupPid))
  | none => pure ()
  -- Check length match
  if pids.length ≠ secrets.length ∨ secrets.length ≠ opens.length then
    throw (.lengthMismatch pids.length secrets.length opens.length)
  -- Generate shares using nested zip
  let shares :=
    (pids.zip (secrets.zip opens)).map fun (pid, sk, op) =>
      let pk_i := S.A sk
      let com  := S.commit pk_i op
      { pid := pid, sk_i := sk, pk_i := pk_i, opening := op, commitPk := com }
  let pk := (shares.map (·.pk_i)).sum
  pure ⟨shares, pk⟩

end IceNine.Protocol
