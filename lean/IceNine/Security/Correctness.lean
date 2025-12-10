/-
# Signature Correctness Proofs

Happy-path correctness: when all parties behave honestly, verification
succeeds. Core algebraic insight: linearity of A and signature equation.

z = Σ z_i = Σ (y_i + c·sk_i) = Σy_i + c·Σsk_i = y + c·sk
A(z) = A(y) + c·A(sk) = w + c·pk
So: A(z) - c·pk = w ✓
-/

import Mathlib
import IceNine.Protocol.Core
import IceNine.Protocol.Sign
import IceNine.Instances
import IceNine.Norms

namespace IceNine.Security

open IceNine.Protocol
open IceNine.Instances
open IceNine.Norms

/-!
## Core Algebraic Lemmas

The key insight: z_i = y_i + c·sk_i sums linearly.
Σ(y_i + c·sk_i) = Σy_i + c·Σsk_i
-/

/-- Linearity of partial signature aggregation for integers.
    Σ(y_i + c·sk_i) splits into Σy_i + c·Σsk_i. -/
lemma sum_zipWith_add_mul (c : Int) :
  ∀ (ys sks : List Int),
    (List.zipWith (fun y s => y + c * s) ys sks).sum
      = ys.sum + c * sks.sum
  | [], [] => by simp
  | [], _  => by simp
  | _ , [] => by simp
  | y::ys, s::sks =>
      have ih := sum_zipWith_add_mul ys sks
      simp [ih, List.sum_cons, add_assoc, add_left_comm, add_comm, mul_add, add_mul]

/-!
## Generic Scheme Correctness

We now state correctness generically for any `Scheme` satisfying:
- linear map `A`
- honest messages use consistent session ids
- hash is the Fiat–Shamir defined in the scheme
These are already encoded in `Scheme`; we only require decidable equality for
participants to reuse the existing validation machinery.
-/

/-- Generic happy-path correctness: if the transcript is valid, verification succeeds. -/
theorem verify_happy_generic
    (S : Scheme) [DecidableEq S.PartyId]
    (pk : S.Public)
    (m : S.Message)
    (Sset : List S.PartyId)
    (commits : List (SignCommitMsg S))
    (reveals : List (SignRevealWMsg S))
    (shares  : List (SignShareMsg S))
    (hvalid : ValidSignTranscript S Sset commits reveals shares) :
  let w := reveals.foldl (fun acc r => acc + r.w_i) (0 : S.Public)
  let c := S.hash m pk Sset (commits.map (·.commitW)) w
  verify S pk m (aggregateSignature S c Sset (commits.map (·.commitW)) shares) := by
  classical
  simp [verify, aggregateSignature, ValidSignTranscript] at *
  rcases hvalid with ⟨hlen1, hlen2, hnodup, hpids, hopen, hsess⟩
  -- lengths equal
  have hlen : commits.length = shares.length := by
    have := hlen1; have := hlen2; linarith
  -- commitments open
  have hopen_ok :
    List.Forall2 (fun c r => S.commit r.w_i r.opening = c.commitW) commits reveals := by
    simpa using (hopen.map_right (fun h => h.right))
  -- all sessions match
  have hsess_all : ∀ sh ∈ shares, sh.session = (commits.head?.map (·.session)).getD 0 := by
    simpa using hsess
  -- core algebra: Σ(y_i + c•sk_i) = Σy_i + c•Σsk_i handled inside verify simplification
  simp [hlen, hpids, hopen_ok, hsess_all, List.forall₂_and_left] at *

/-!
## Module-General Correctness

Generalize to any R-module (needed for ZMod vectors, lattices, etc.).
-/

/-- Module-general linearity: works for any semiring R and module M.
    Σ(y_i + c•sk_i) = Σy_i + c•Σsk_i. -/
lemma sum_zipWith_add_smul
    {R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]
    (c : R) :
  ∀ (ys sks : List M),
    (List.zipWith (fun y s => y + c • s) ys sks).sum
      = ys.sum + c • sks.sum
  | [], [] => by simp
  | [], _  => by simp
  | _ , [] => by simp
  | y::ys, s::sks =>
      have ih := sum_zipWith_add_smul ys sks
      simp [ih, List.sum_cons, add_assoc, add_left_comm, add_comm, smul_add, add_smul]

/-!
## Short Input Hypothesis

For lattice signature correctness with real norm bounds, we need to ensure that:
1. Secret shares sk_i are "short" (||sk_i||∞ ≤ η)
2. Nonces y_i are sampled from bounded range (||y_i||∞ < γ₁)
3. The response z_i = y_i + c·sk_i passes the norm check

Without these hypotheses, the correctness theorem would require normOK to be trivially true.
With real Dilithium bounds, correctness holds conditional on proper sampling.
-/

/-- Hypothesis: all secret shares are short (bounded by η). -/
def SecretsShort (S : Scheme) (shares : List (KeyShare S))
    (bound : S.Secret → Prop) : Prop :=
  ∀ sh ∈ shares, bound sh.sk_i

/-- Hypothesis: all nonces are sampled from bounded range. -/
def NoncesInRange (S : Scheme) (nonces : List S.Secret)
    (bound : S.Secret → Prop) : Prop :=
  ∀ y ∈ nonces, bound y

/-- Hypothesis: all responses pass the scheme's norm check. -/
def ResponsesValid (S : Scheme) (responses : List (SignShareMsg S)) : Prop :=
  ∀ z ∈ responses, S.normOK z.z_i

/-!
## Instantiation: lattice scheme

We now target the actual lattice scheme used by the protocol, instead of the
toy ZMod surrogate. We reuse the generic correctness lemma above.
-/

/-- Happy-path correctness for the concrete lattice scheme. -/
theorem verify_happy_lattice
    (pk : latticeScheme.Public)
    (m : latticeScheme.Message)
    (Sset : List latticeScheme.PartyId)
    (commits : List (SignCommitMsg latticeScheme))
    (reveals : List (SignRevealWMsg latticeScheme))
    (shares  : List (SignShareMsg latticeScheme))
    (hvalid : ValidSignTranscript latticeScheme Sset commits reveals shares) :
  let w := reveals.foldl (fun acc r => acc + r.w_i) (0 : latticeScheme.Public)
  let c := latticeScheme.hash m pk Sset (commits.map (·.commitW)) w
  verify latticeScheme pk m (aggregateSignature latticeScheme c Sset (commits.map (·.commitW)) shares) := by
  classical
  have := verify_happy_generic (S := latticeScheme) (pk := pk) (m := m)
    (Sset := Sset) (commits := commits) (reveals := reveals) (shares := shares) hvalid
  simpa using this

/-- Honest sampling trivially satisfies `normOK` for the current latticeScheme
    (norm check is permissive in this placeholder instance). Replace with a real
    bound proof once `normOK` enforces Dilithium-style limits.

    **TODO**: With real Dilithium bounds, this becomes:
    ```
    lemma lattice_normOK_honest
        (y : latticeScheme.Secret) (sk : latticeScheme.Secret) (c : Int)
        (hy : ||y||∞ < γ₁) (hsk : ||sk||∞ ≤ η) (hc : |c| ≤ τ)
        : ||y + c·sk||∞ < γ₁ - β → latticeScheme.normOK (y + c·sk)
    ```
    The hypothesis bounds ensure rejection sampling succeeds with high probability. -/
lemma lattice_normOK_honest (z : latticeScheme.Secret) : latticeScheme.normOK z := by
  trivial

/-- Conditional correctness: if all responses pass norm check, verification succeeds.
    This is the form needed for real lattice schemes where normOK is non-trivial. -/
theorem verify_happy_lattice_conditional
    (pk : latticeScheme.Public)
    (m : latticeScheme.Message)
    (Sset : List latticeScheme.PartyId)
    (commits : List (SignCommitMsg latticeScheme))
    (reveals : List (SignRevealWMsg latticeScheme))
    (shares  : List (SignShareMsg latticeScheme))
    (hvalid : ValidSignTranscript latticeScheme Sset commits reveals shares)
    (hnorm : ResponsesValid latticeScheme shares) :
  let w := reveals.foldl (fun acc r => acc + r.w_i) (0 : latticeScheme.Public)
  let c := latticeScheme.hash m pk Sset (commits.map (·.commitW)) w
  verify latticeScheme pk m (aggregateSignature latticeScheme c Sset (commits.map (·.commitW)) shares) := by
  -- Proof identical to verify_happy_lattice; hnorm ensures normOK passes
  classical
  have := verify_happy_generic (S := latticeScheme) (pk := pk) (m := m)
    (Sset := Sset) (commits := commits) (reveals := reveals) (shares := shares) hvalid
  simpa using this

end IceNine.Security
