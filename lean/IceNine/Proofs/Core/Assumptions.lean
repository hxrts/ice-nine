/-
# Security Assumptions

Abstract security assumptions for threshold signature proofs, stated in a
post-quantum setting. We expose a small catalog of NIST PQC (Dilithium-style)
parameter sets via `PQSecurityLevel` (L1/L3/L5) and a helper
`mkLatticeAssumptions` that constructs the assumption bundle from that level.
In practice you choose a level and provide the scheme-specific hardness claims
(`hashQROM`, `commitPQBinding`, `normLeakageBound`, and corruption bound).
- Quantum Random Oracle model (QROM) for the hash function
- Commitment binding against quantum adversaries
- Norm bounds for lattice security (SIS/MLWE hardness)
- Corruption bounds for threshold security

All security theorems are parameterized by these assumptions.

## Lattice Hardness Problems

The security of lattice-based signatures reduces to two computational problems:

### Short Integer Solution (SIS)
Given A ∈ Z_q^{n×m}, find z ∈ Z^m with ||z|| ≤ β and Az = 0 mod q.
Hardness: For appropriate parameters, as hard as worst-case lattice problems.

**Reference**: Ajtai, "Generating Hard Instances of Lattice Problems", STOC 1996.

### Module Learning With Errors (MLWE)
Distinguish (A, As + e) from (A, u) where A is uniform, s,e are small.
This generalizes Ring-LWE to module lattices for flexible security/efficiency.

**Reference**: Langlois & Stehlé, "Worst-case to Average-case Reductions
for Module Lattices", Designs, Codes and Cryptography, 2015.
-/

import IceNine.Protocol.Core.Core
import IceNine.Protocol.Sign.Types
import IceNine.Protocol.DKG.Core
import IceNine.Instances
import IceNine.Proofs.Probability.Commitment
import IceNine.Proofs.Probability.Indistinguishability
import IceNine.Proofs.Probability.Rejection
import IceNine.Proofs.Probability.RepeatUntil
import Mathlib

set_option autoImplicit false

namespace IceNine.Proofs

open IceNine.Protocol
open IceNine.Protocol.NormBounded
open IceNine.Protocol.ThresholdConfig
open IceNine.Instances
open IceNine.Proofs.Probability

/-!
## Short Integer Solution (SIS) Problem

SIS is the foundation for lattice signature unforgeability.
Finding a forgery ≈ finding a short vector in the kernel of A.
-/

/-- SIS problem parameters -/
structure SISParams where
  /-- Lattice dimension (rows of A) -/
  n : Nat
  /-- Number of columns of A -/
  m : Nat
  /-- Modulus -/
  q : Nat
  /-- Solution norm bound -/
  beta : Nat
  /-- Security level in bits (e.g., 128, 192, 256) -/
  securityParam : Nat := 128

/-- Heuristic parameter-growth requirement for classic SIS hardness.

This condition does **not** hold for standard Dilithium parameter sets; Dilithium’s
security relies on different module/ring assumptions (MLWE/MSIS).
-/
def SISParams.mLarge (p : SISParams) : Prop :=
  p.m > p.n * Nat.log2 p.q

/-- SIS problem instance: public matrix A -/
structure SISInstance (p : SISParams) where
  /-- Public matrix A ∈ Z_q^{n×m} -/
  A : Fin p.n → Fin p.m → ZMod p.q

/-- A solution to SIS: short vector z with Az = 0 -/
structure SISSolution (p : SISParams) (inst : SISInstance p) where
  /-- Solution vector z ∈ Z^m -/
  z : Fin p.m → Int
  /-- z is short: ||z||∞ ≤ β -/
  z_short : ∀ i, Int.natAbs (z i) ≤ p.beta
  /-- z is nonzero -/
  z_nonzero : ∃ i, z i ≠ 0
  /-- Az = 0 mod q -/
  Az_zero : ∀ i : Fin p.n,
    (Finset.univ.sum fun j => inst.A i j * (z j : ZMod p.q)) = 0

/-- SIS hardness assumption: no efficient algorithm finds solutions -/
axiom SISHard (p : SISParams) : Prop

/-- NIST PQC (Dilithium2-ish) SIS parameters, Level 1 (~128-bit)
    NOTE: The m_large constraint is not satisfied by standard Dilithium parameters.
    Dilithium's security relies on different lattice hardness arguments (MLWE/MSIS). -/
def sisL1 : SISParams :=
  { n := 256, m := 512, q := 8380417, beta := 78, securityParam := 128 }

/-- NIST PQC (Dilithium3-ish) SIS parameters, Level 3 (~192-bit) -/
def sisL3 : SISParams :=
  { n := 256, m := 512, q := 8380417, beta := 120, securityParam := 192 }

/-- NIST PQC (Dilithium5-ish) SIS parameters, Level 5 (~256-bit) -/
def sisL5 : SISParams :=
  { n := 256, m := 512, q := 8380417, beta := 196, securityParam := 256 }

/-!
## Module Learning With Errors (MLWE) Problem

MLWE underlies key secrecy: recovering the secret key from
public key requires solving MLWE.
-/

/-- MLWE problem parameters -/
structure MLWEParams where
  /-- Ring dimension (degree of polynomial ring R_q = Z_q[X]/(X^n + 1)) -/
  n : Nat
  /-- Module rank (number of ring elements in secret) -/
  k : Nat
  /-- Modulus -/
  q : Nat
  /-- Error distribution parameter (std dev for Gaussian, bound for uniform) -/
  eta : Nat

/-- MLWE instance: public (A, b = As + e) -/
structure MLWEInstance (p : MLWEParams) where
  /-- Public matrix A ∈ R_q^{k×k} (k×k matrix of polynomials) -/
  A : Fin p.k → Fin p.k → (Fin p.n → ZMod p.q)
  /-- Public vector b = As + e ∈ R_q^k -/
  b : Fin p.k → (Fin p.n → ZMod p.q)

/-- MLWE secret and error -/
structure MLWESecret (p : MLWEParams) where
  /-- Secret vector s ∈ R_q^k with small coefficients -/
  s : Fin p.k → (Fin p.n → Int)
  /-- Error vector e ∈ R_q^k with small coefficients -/
  e : Fin p.k → (Fin p.n → Int)
  /-- s is short -/
  s_short : ∀ i j, Int.natAbs (s i j) ≤ p.eta
  /-- e is short -/
  e_short : ∀ i j, Int.natAbs (e i j) ≤ p.eta

/-- MLWE hardness: distinguishing (A, As+e) from (A, u) is hard -/
axiom MLWEHard (p : MLWEParams) : Prop

/-- Ring-LWE is MLWE with k=1 (single polynomial) -/
def RLWEParams (n q eta : Nat) : MLWEParams :=
  { n := n, k := 1, q := q, eta := eta }

/-- NIST PQC (Dilithium2) MLWE parameters, Level 1 (~128-bit) -/
def mlweL1 : MLWEParams :=
  { n := 256, k := 4, q := 8380417, eta := 2 }

/-- NIST PQC (Dilithium3) MLWE parameters, Level 3 (~192-bit) -/
def mlweL3 : MLWEParams :=
  { n := 256, k := 6, q := 8380417, eta := 4 }

/-- NIST PQC (Dilithium5) MLWE parameters, Level 5 (~256-bit) -/
def mlweL5 : MLWEParams :=
  { n := 256, k := 8, q := 8380417, eta := 4 }

/-- Security levels aligned with NIST PQC Dilithium parameter sets. -/
inductive PQSecurityLevel
  | L1 | L3 | L5
  deriving DecidableEq, Repr

/-- Pick SIS params by security level. -/
def sisParamsOfLevel : PQSecurityLevel → SISParams
  | .L1 => sisL1
  | .L3 => sisL3
  | .L5 => sisL5

/-- Pick MLWE params by security level. -/
def mlweParamsOfLevel : PQSecurityLevel → MLWEParams
  | .L1 => mlweL1
  | .L3 => mlweL3
  | .L5 => mlweL5

/-!
## Rejection Sampling Model

The signing protocol uses rejection sampling to ensure responses don't leak
information about the secret key.

In this file we:
- define the *distributions* induced by the pure protocol code (via `PMF`)
- keep the *security properties* (hiding / response-independence) as explicit
  assumptions to be proved later under concrete crypto assumptions.

**Background**: In Dilithium-style signatures, the response z = y + c·s must be
independent of s. Rejection sampling achieves this by:
1. Sampling y from a wide distribution
2. Rejecting z if ||z||∞ ≥ γ₁ - β (where β = τ·η)
3. Accepted z values follow a distribution independent of s

**Reference**: Lyubashevsky, "Fiat-Shamir with Aborts", ASIACRYPT 2009.
-/

/- A “distribution family” over `α`, indexed by a security parameter `κ`,
is now modeled by `Probability.DistFamily`. -/

/-- Acceptance-rate bound for local rejection sampling.

We model “expected iterations ≈ κ” as an explicit bound on **rejection**
probability for the *candidate* response distribution.

This is designed to connect directly to `Probability.Dist.repeatOption`, whose
failure probability is exactly `(Pr[reject])^n`. -/
def AcceptanceRateBound (S : Scheme)
    [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (nonceDist : DistFamily (S.Secret × S.Secret))
    (expectedIterations : Nat) : Prop :=
  expectedIterations > 0 ∧
    ∀ (bindingFactor : S.Scalar) (c : S.Challenge) (s : S.Secret) (κ : Nat),
      Dist.prob
          (candidateResponseDist S nonceDist bindingFactor c s κ)
          (acceptSet S cfg)ᶜ
        ≤ ((expectedIterations - 1 : Nat) : ENNReal) / (expectedIterations : ENNReal)

/-- Failure probability of a truncated “try up to `n` times” rejection loop, bounded using
`AcceptanceRateBound`. -/
theorem AcceptanceRateBound.failureProb_repeatOption_none_le
    {S : Scheme} [NormBounded S.Secret]
    {cfg : ThresholdConfig}
    {nonceDist : DistFamily (S.Secret × S.Secret)}
    {expectedIterations : Nat}
    (h : AcceptanceRateBound S cfg nonceDist expectedIterations)
    (bindingFactor : S.Scalar) (c : S.Challenge) (s : S.Secret) (κ n : Nat) :
    Dist.prob
        (Dist.repeatOption
          (candidateResponseDist S nonceDist bindingFactor c s κ)
          (acceptSet S cfg) n)
        {none}
      ≤ (((expectedIterations - 1 : Nat) : ENNReal) / (expectedIterations : ENNReal)) ^ n := by
  have hrej :
      Dist.prob
          (candidateResponseDist S nonceDist bindingFactor c s κ)
          (acceptSet S cfg)ᶜ
        ≤ ((expectedIterations - 1 : Nat) : ENNReal) / (expectedIterations : ENNReal) :=
    h.2 bindingFactor c s κ
  simpa [Dist.prob_repeatOption_none] using (ENNReal.pow_le_pow_left hrej (n := n))


/-- Distribution semantics for the bounded local rejection loop.

We model “try up to `cfg.maxLocalAttempts` times” as `Dist.repeatOption` on the
candidate-response distribution.
-/
noncomputable def localRejectionDist (S : Scheme)
    [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (nonceDist : DistFamily (S.Secret × S.Secret))
    (bindingFactor : S.Scalar)
    (c : S.Challenge)
    (s : S.Secret)
    (κ : Nat) : Probability.Dist (Option S.Secret) :=
  Dist.repeatOption
    (candidateResponseDist S nonceDist bindingFactor c s κ)
    (acceptSet S cfg)
    cfg.maxLocalAttempts

/-- Abort probability bound for the bounded local rejection loop, derived from `AcceptanceRateBound`. -/
theorem AcceptanceRateBound.failureProb_localRejectionDist_none_le
    {S : Scheme} [NormBounded S.Secret]
    {cfg : ThresholdConfig}
    {nonceDist : DistFamily (S.Secret × S.Secret)}
    {expectedIterations : Nat}
    (h : AcceptanceRateBound S cfg nonceDist expectedIterations)
    (bindingFactor : S.Scalar) (c : S.Challenge) (s : S.Secret) (κ : Nat) :
    Dist.prob (localRejectionDist S cfg nonceDist bindingFactor c s κ) {none}
      ≤ (((expectedIterations - 1 : Nat) : ENNReal) / (expectedIterations : ENNReal)) ^ cfg.maxLocalAttempts := by
  simpa [localRejectionDist] using
    (AcceptanceRateBound.failureProb_repeatOption_none_le
      (S := S) (cfg := cfg) (nonceDist := nonceDist) (expectedIterations := expectedIterations)
      h bindingFactor c s κ cfg.maxLocalAttempts)

/-- Turn a uniform acceptance lower bound into an `AcceptanceRateBound`.

If every candidate response is accepted with probability at least `1/expectedIterations`, then
the rejection probability is at most `(expectedIterations - 1) / expectedIterations`.
-/
theorem AcceptanceRateBound.of_accept_prob_ge_one_div
    {S : Scheme} [NormBounded S.Secret]
    {cfg : ThresholdConfig}
    {nonceDist : DistFamily (S.Secret × S.Secret)}
    {expectedIterations : Nat}
    (hpos : expectedIterations > 0)
    (hacc :
      ∀ (bindingFactor : S.Scalar) (c : S.Challenge) (s : S.Secret) (κ : Nat),
        (1 : ENNReal) / (expectedIterations : ENNReal) ≤
          Dist.prob (candidateResponseDist S nonceDist bindingFactor c s κ) (acceptSet S cfg)) :
    AcceptanceRateBound S cfg nonceDist expectedIterations := by
  refine ⟨hpos, ?_⟩
  intro bindingFactor c s κ
  -- Shorthand for the candidate distribution at security parameter `κ`.
  set d : Probability.Dist S.Secret := candidateResponseDist S nonceDist bindingFactor c s κ

  have hrej : Dist.prob d (acceptSet S cfg)ᶜ = (1 : ENNReal) - Dist.prob d (acceptSet S cfg) := by
    simpa [d] using (Dist.prob_compl (d := d) (s := acceptSet S cfg))

  have htsub : (1 : ENNReal) - Dist.prob d (acceptSet S cfg) ≤
      (1 : ENNReal) - (1 : ENNReal) / (expectedIterations : ENNReal) := by
    exact tsub_le_tsub_left (hacc bindingFactor c s κ) 1

  have hE0 : (expectedIterations : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)

  have hbTop : (1 : ENNReal) / (expectedIterations : ENNReal) ≠ (⊤ : ENNReal) := by
    -- `1 / E` is finite when `E ≠ 0`.
    exact ENNReal.div_ne_top (h1 := by simp) (h2 := hE0)

  have hcast : (expectedIterations : ENNReal) - 1 + 1 = (expectedIterations : ENNReal) := by
    have hle : (1 : ENNReal) ≤ (expectedIterations : ENNReal) := by
      have : 1 ≤ expectedIterations := Nat.succ_le_of_lt hpos
      exact_mod_cast this
    exact tsub_add_cancel_of_le hle

  have hone : (1 : ENNReal) - (1 : ENNReal) / (expectedIterations : ENNReal) =
      ((expectedIterations - 1 : Nat) : ENNReal) / (expectedIterations : ENNReal) := by
    have hsum :
        ((expectedIterations - 1 : Nat) : ENNReal) / (expectedIterations : ENNReal) +
            (1 : ENNReal) / (expectedIterations : ENNReal) = 1 := by
      calc
        ((expectedIterations - 1 : Nat) : ENNReal) / (expectedIterations : ENNReal) +
            (1 : ENNReal) / (expectedIterations : ENNReal)
            = (((expectedIterations - 1 : Nat) : ENNReal) + 1) / (expectedIterations : ENNReal) := by
                exact (ENNReal.div_add_div_same
                  (a := ((expectedIterations - 1 : Nat) : ENNReal))
                  (b := (1 : ENNReal))
                  (c := (expectedIterations : ENNReal)))
        _ = (expectedIterations : ENNReal) / (expectedIterations : ENNReal) := by
              simp [hcast]
        _ = 1 := by
              exact ENNReal.div_self hE0 (ENNReal.natCast_ne_top expectedIterations)
    exact ENNReal.sub_eq_of_eq_add (hb := hbTop) hsum.symm

  -- Conclude: `Pr[reject] = 1 - Pr[accept] ≤ 1 - 1/E = (E-1)/E`.
  calc
    Dist.prob d (acceptSet S cfg)ᶜ
        = (1 : ENNReal) - Dist.prob d (acceptSet S cfg) := hrej
    _ ≤ (1 : ENNReal) - (1 : ENNReal) / (expectedIterations : ENNReal) := htsub
    _ = ((expectedIterations - 1 : Nat) : ENNReal) / (expectedIterations : ENNReal) := hone

/-- Acceptance probability bound for rejection sampling.
    Guarantees signing terminates in expected O(κ) attempts.

    For Dilithium parameters, acceptance probability is approximately 1/4,
    so κ ≈ 4 expected iterations. -/
structure AcceptanceProbability (S : Scheme) [NormBounded S.Secret] where
  /-- Public threshold configuration (drives the local acceptance predicate). -/
  cfg : ThresholdConfig
  /-- Distribution of fresh nonce pairs `(y_hiding, y_binding)`. -/
  nonceDist : DistFamily (S.Secret × S.Secret)
  /-- Upper bound on expected number of rejection sampling iterations. -/
  expectedIterations : Nat
  /-- Bound is valid (expectedIterations > 0). -/
  bound_valid : expectedIterations > 0
  /-- Rejection probability bound for honest parties with short secrets. -/
  acceptance_rate : AcceptanceRateBound S cfg nonceDist expectedIterations

/-- Build an `AcceptanceProbability` record from a uniform `1/expectedIterations` acceptance lower bound. -/
def AcceptanceProbability.of_accept_prob_ge_one_div
    {S : Scheme} [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (nonceDist : DistFamily (S.Secret × S.Secret))
    (expectedIterations : Nat)
    (hpos : expectedIterations > 0)
    (hacc :
      ∀ (bindingFactor : S.Scalar) (c : S.Challenge) (s : S.Secret) (κ : Nat),
        (1 : ENNReal) / (expectedIterations : ENNReal) ≤
          Dist.prob (candidateResponseDist S nonceDist bindingFactor c s κ) (acceptSet S cfg)) :
    AcceptanceProbability S :=
  { cfg := cfg
    nonceDist := nonceDist
    expectedIterations := expectedIterations
    bound_valid := hpos
    acceptance_rate :=
      AcceptanceRateBound.of_accept_prob_ge_one_div
        (S := S) (cfg := cfg) (nonceDist := nonceDist)
        (expectedIterations := expectedIterations)
        hpos hacc }

/-- Response independence assumptions for rejection sampling.

The protocol’s accepted response distribution is the candidate response
conditioned on the local acceptance predicate (`acceptSet`), which may depend on
`κ` via the configuration `cfg κ`.

We keep the hard part (candidate responses are statistically close across
secrets) as an explicit assumption (`candidate_indist`), and derive the usual
accepted-response independence claim via a general conditioning lemma, assuming:

- a κ-indexed nonzero lower bound `accept_lb κ` on acceptance probability, and
- an inverse-polynomial bound on `(accept_lb κ)⁻¹` (`accept_inv_poly`).
-/
structure ResponseIndependence (S : Scheme) [NormBounded S.Secret] where
  /-- Public threshold configuration family (drives the local acceptance predicate). -/
  cfg : Nat → ThresholdConfig
  /-- Distribution of fresh nonce pairs `(y_hiding, y_binding)`. -/
  nonceDist : DistFamily (S.Secret × S.Secret)
  /-- Secrets for which we claim response independence (typically, “short” secrets). -/
  secretOK : Set S.Secret := Set.univ
  /-- Admissible public parameters (e.g. bounded challenges / binding factors). -/
  publicOK : Nat → S.Scalar → S.Challenge → Prop := fun _ _ _ => True
  /-- A κ-indexed lower bound on acceptance probability. -/
  accept_lb : Nat → ENNReal
  /-- The lower bound is nonzero for every `κ`. -/
  accept_lb_ne_zero : ∀ κ, accept_lb κ ≠ 0
  /-- The inverse lower bound is polynomially bounded (so conditioning preserves negligibility). -/
  accept_inv_poly : ∃ d : Nat, ∀ᶠ κ in Filter.atTop, (accept_lb κ)⁻¹ ≤ (κ : ENNReal) ^ d
  /-- Acceptance probability is bounded below by `accept_lb κ` for admissible parameters and secrets. -/
  accept_prob_ge :
    ∀ (bindingFactor : S.Scalar) (c : S.Challenge) (s : S.Secret) (κ : Nat),
      publicOK κ bindingFactor c → s ∈ secretOK →
        accept_lb κ ≤
          Dist.prob (candidateResponseDist S nonceDist bindingFactor c s κ) (acceptSet S (cfg κ))
  /-- Candidate responses are indistinguishable across secret keys (statistical, first). -/
  candidate_indist :
    ∀ (bindingFactor : S.Scalar) (c : S.Challenge) (s₁ s₂ : S.Secret),
      (∀ᶠ κ in Filter.atTop, publicOK κ bindingFactor c) →
        s₁ ∈ secretOK → s₂ ∈ secretOK →
          Indistinguishable
            (candidateResponseDist S nonceDist bindingFactor c s₁)
            (candidateResponseDist S nonceDist bindingFactor c s₂)

theorem ResponseIndependence.independence
    {S : Scheme} [NormBounded S.Secret]
    (h : ResponseIndependence S)
    (bindingFactor : S.Scalar) (c : S.Challenge) (s₁ s₂ : S.Secret)
    (hpub : ∀ᶠ κ in Filter.atTop, h.publicOK κ bindingFactor c)
    (hs₁ : s₁ ∈ h.secretOK)
    (hs₂ : s₂ ∈ h.secretOK) :
    Indistinguishable
      (acceptedResponseDist S h.cfg h.nonceDist bindingFactor c s₁)
      (acceptedResponseDist S h.cfg h.nonceDist bindingFactor c s₂) := by
  classical
  -- Start from candidate indistinguishability.
  rcases h.candidate_indist bindingFactor c s₁ s₂ hpub hs₁ hs₂ with ⟨ε, hεneg, hεclose⟩

  -- Conditioning blowup (when `publicOK κ` holds).
  let εcond : Nat → ENNReal := fun κ => 2 * ε κ / h.accept_lb κ
  have hεcond : Negligible εcond :=
    Negligible.mul_invpoly (ε := ε) (α0 := h.accept_lb) hεneg h.accept_inv_poly

  refine
    ⟨fun κ => if h.publicOK κ bindingFactor c then εcond κ else 1,
      ?_, ?_⟩

  · -- Negligible: eventually `publicOK κ` holds.
    have hEq :
        (fun κ => if h.publicOK κ bindingFactor c then εcond κ else 1)
          =ᶠ[Filter.atTop] εcond := by
      filter_upwards [hpub] with κ hpubκ
      simp [hpubκ]
    exact Negligible.eventually_eq (h := hεcond) hEq

  · intro κ
    classical
    by_cases hpubκ : h.publicOK κ bindingFactor c
    · -- Under admissible public parameters, use the pointwise conditioning lemma.
      have hαp : h.accept_lb κ ≤
          Dist.prob (candidateResponseDist S h.nonceDist bindingFactor c s₁ κ)
            (acceptSet S (h.cfg κ)) :=
        h.accept_prob_ge bindingFactor c s₁ κ hpubκ hs₁

      have hαq : h.accept_lb κ ≤
          Dist.prob (candidateResponseDist S h.nonceDist bindingFactor c s₂ κ)
            (acceptSet S (h.cfg κ)) :=
        h.accept_prob_ge bindingFactor c s₂ κ hpubκ hs₂

      have hcond : StatClose
          (acceptedResponseDist S h.cfg h.nonceDist bindingFactor c s₁ κ)
          (acceptedResponseDist S h.cfg h.nonceDist bindingFactor c s₂ κ)
          (εcond κ) :=
        StatClose.acceptedResponseDist_of_prob_ge
          (S := S)
          (cfg := h.cfg)
          (nonceDist := h.nonceDist)
          (bindingFactor := bindingFactor)
          (challenge := c)
          (sk₁ := s₁) (sk₂ := s₂) (κ := κ)
          (hclose := hεclose κ)
          (hα0 := h.accept_lb_ne_zero κ)
          (hprob₁ := hαp)
          (hprob₂ := hαq)

      simpa [hpubκ] using hcond

    · -- Outside `publicOK`, use the trivial bound `≤ 1`.
      intro s
      have hp1 :
          Dist.prob (acceptedResponseDist S h.cfg h.nonceDist bindingFactor c s₁ κ) s ≤ 1 := by
        have hmono := Dist.prob_mono
          (d := acceptedResponseDist S h.cfg h.nonceDist bindingFactor c s₁ κ)
          (s := s) (t := Set.univ) (by intro _ hx; trivial)
        have huniv :
            Dist.prob (acceptedResponseDist S h.cfg h.nonceDist bindingFactor c s₁ κ) (Set.univ : Set S.Secret) = 1 := by
          classical
          simp [Dist.prob]
        simpa [huniv] using hmono
      have hq1 :
          Dist.prob (acceptedResponseDist S h.cfg h.nonceDist bindingFactor c s₂ κ) s ≤ 1 := by
        have hmono := Dist.prob_mono
          (d := acceptedResponseDist S h.cfg h.nonceDist bindingFactor c s₂ κ)
          (s := s) (t := Set.univ) (by intro _ hx; trivial)
        have huniv :
            Dist.prob (acceptedResponseDist S h.cfg h.nonceDist bindingFactor c s₂ κ) (Set.univ : Set S.Secret) = 1 := by
          classical
          simp [Dist.prob]
        simpa [huniv] using hmono
      have habs : absSubENNReal
          (Dist.prob (acceptedResponseDist S h.cfg h.nonceDist bindingFactor c s₁ κ) s)
          (Dist.prob (acceptedResponseDist S h.cfg h.nonceDist bindingFactor c s₂ κ) s) ≤ 1 := by
        -- `a - b ≤ a ≤ 1` and `b - a ≤ b ≤ 1`.
        unfold absSubENNReal
        refine max_le ?_ ?_
        · exact (tsub_le_self).trans hp1
        · exact (tsub_le_self).trans hq1

      simpa [hpubκ] using habs


/-- Standard Dilithium acceptance probability (≈ 1/4, so expect 4 iterations) -/
def dilithiumAcceptance (S : Scheme) [NormBounded S.Secret]
    (cfg : ThresholdConfig)
    (nonceDist : DistFamily (S.Secret × S.Secret))
    (h : AcceptanceRateBound S cfg nonceDist 4) :
    AcceptanceProbability S :=
  { cfg := cfg
    nonceDist := nonceDist
    expectedIterations := 4
    bound_valid := by decide
    acceptance_rate := h }

/-!
## Security Reduction Structure

Documents how signature security reduces to SIS/MLWE hardness.
-/

/-- Reduction from signature forgery to SIS.
    If an adversary can forge signatures, we can solve SIS. -/
structure ForgerToSIS (S : Scheme) (p : SISParams) where
  /-- The forger's advantage (probability of forgery) -/
  forgerAdvantage : Real
  /-- Number of signing queries the forger makes -/
  signingQueries : Nat
  /-- Number of hash queries (random oracle) -/
  hashQueries : Nat
  /-- The resulting SIS solver's advantage -/
  sisAdvantage : Real
  /-- Reduction tightness: SIS advantage ≥ forger advantage / loss factor -/
  reduction_tight :
    sisAdvantage ≥ forgerAdvantage / (hashQueries * signingQueries)

/-- Reduction from key recovery to MLWE.
    If an adversary can recover secret key, we can solve MLWE. -/
structure KeyRecoveryToMLWE (S : Scheme) (p : MLWEParams) where
  /-- The key recovery advantage -/
  keyRecoveryAdvantage : Real
  /-- The resulting MLWE distinguisher's advantage -/
  mlweAdvantage : Real
  /-- Reduction is tight for key recovery -/
  reduction_tight : mlweAdvantage ≥ keyRecoveryAdvantage

/-!
## Collision Resistance

Hash-based commitments derive binding from collision resistance of the underlying
hash function. We axiomatize CR as a property that can be assumed for concrete
hash instantiations (SHA3, SHAKE, etc.).
-/

/-- Collision resistance assumption for a hash function.
    States that finding distinct inputs with the same output is computationally infeasible.

    For hash-based commitments Com(x, r) = H(x || r):
    - Binding follows from CR: if Com(x₁, r₁) = Com(x₂, r₂), then x₁ || r₁ = x₂ || r₂
    - This implies x₁ = x₂ (the binding property)

    **Reference**: Halevi & Micali, "Practical and Provably-Secure Commitment Schemes
    from Collision-Free Hashing", CRYPTO 1996. -/
structure CollisionResistant {α β : Type*} (H : α → β) : Prop where
  /-- No efficient algorithm can find x₁ ≠ x₂ with H(x₁) = H(x₂) -/
  no_collisions : ∀ x₁ x₂, H x₁ = H x₂ → x₁ = x₂

/-- Collision resistance for the scheme's commitment function.
    This is sufficient for binding: CR → Binding. -/
def commitmentCR (S : Scheme) : Prop :=
  -- The commitment function is collision resistant when viewed as H(x || opening)
  S.hashCollisionResistant

/-!
## Hiding Assumption

Hash-based commitments are not perfectly hiding. They provide computational hiding
under the Random Oracle Model (ROM). We explicitly axiomatize this assumption
since it cannot be proven from first principles.

**WARNING**: This is a stronger assumption than collision resistance. Protocols
that require hiding (e.g., for zero-knowledge properties) must explicitly include
this assumption in their security theorems.
-/

/-- Hiding assumption for commitments.
    States that Com(x₁, r) and Com(x₂, r') are computationally indistinguishable
    for random r, r'.

    For hash-based commitments, this requires the Random Oracle Model.
    For Pedersen commitments, this holds perfectly (information-theoretically).

    **NOT FORMALIZED**: We cannot prove hiding in Lean without probabilistic
    reasoning. This is an explicit axiom that must be assumed. -/
structure HidingAssumption (S : Scheme) where
  /-- Distribution of random openings. -/
  openingDist : DistFamily S.Opening
  /-- Commitments reveal nothing about the committed value (ROM / crypto assumption). -/
  isHiding :
    ∀ x₁ x₂ : S.Public,
      CompIndistinguishable (commitDist S openingDist x₁) (commitDist S openingDist x₂)

/-!
## Assumption Bundle

Packages all cryptographic assumptions needed for security proofs.
Concrete instantiations must prove these properties hold.
-/

/-- Security assumptions for threshold signature scheme. -/
structure Assumptions (S : Scheme) where
  /-- Hash behaves as a quantum random oracle (QROM) for Fiat-Shamir. -/
  hashRO            : Prop
  /-- Commitment scheme is collision resistant (implies binding). -/
  commitCR          : Prop := commitmentCR S
  /-- Binding for the hash-based commitment (collision resistance of digest). -/
  hashBinding       : IceNine.Instances.HashBinding
  /-- Commitment hiding (requires ROM; NOT formally proven). -/
  commitHiding      : HidingAssumption S
  /-- Norm bounds prevent leakage in lattice setting. -/
  normLeakageBound  : Prop
  /-- Max corrupted parties (must be < threshold for security). -/
  corruptionBound   : Nat
  /-- SIS parameters for unforgeability (post-quantum). -/
  sisParams : Option SISParams := none
  /-- MLWE parameters for key secrecy (post-quantum). -/
  mlweParams : Option MLWEParams := none

/-- Full lattice assumptions including SIS and MLWE -/
structure LatticeAssumptions (S : Scheme) extends Assumptions S where
  /-- SIS instance derived from scheme -/
  sisInst : SISParams
  /-- MLWE instance derived from scheme -/
  mlweInst : MLWEParams
  /-- SIS is hard for these parameters -/
  sis_hard : SISHard sisInst
  /-- MLWE is hard for these parameters -/
  mlwe_hard : MLWEHard mlweInst

/-- Instantiate lattice assumptions from a security level. -/
def mkLatticeAssumptions
  (S : Scheme)
  (lvl : PQSecurityLevel)
  (hashRO : Prop)
  (commitCR : Prop)
  (hashBinding : IceNine.Instances.HashBinding)
  (commitHiding : HidingAssumption S)
  (normLeakageBound : Prop)
  (corruptionBound : Nat)
  (sis_hard : SISHard (sisParamsOfLevel lvl))
  (mlwe_hard : MLWEHard (mlweParamsOfLevel lvl))
  : LatticeAssumptions S :=
{ hashRO := hashRO
  commitCR := commitCR
  hashBinding := hashBinding
  commitHiding := commitHiding
  normLeakageBound := normLeakageBound
  corruptionBound := corruptionBound
  sisParams := some (sisParamsOfLevel lvl)
  mlweParams := some (mlweParamsOfLevel lvl)
  sisInst := sisParamsOfLevel lvl
  mlweInst := mlweParamsOfLevel lvl
  sis_hard := sis_hard
  mlwe_hard := mlwe_hard }

/-- Default lattice assumptions for our concrete latticeScheme at Level 1. -/
def latticeAssumptionsL1
  (hashBinding : IceNine.Instances.HashBinding)
  (hashRO : Prop)
  (commitCR : Prop)
  (commitHiding : HidingAssumption (IceNine.Instances.latticeScheme (hb := hashBinding)))
  (normLeakageBound : Prop)
  (corruptionBound : Nat)
  (sis_hard : SISHard (sisParamsOfLevel PQSecurityLevel.L1))
  (mlwe_hard : MLWEHard (mlweParamsOfLevel PQSecurityLevel.L1)) :
  LatticeAssumptions (IceNine.Instances.latticeScheme (hb := hashBinding)) :=
  mkLatticeAssumptions (S := IceNine.Instances.latticeScheme (hb := hashBinding)) PQSecurityLevel.L1
    hashRO
    commitCR
    hashBinding
    commitHiding
    normLeakageBound
    corruptionBound
    sis_hard
    mlwe_hard

/-!
## Security Theorems

Main security guarantees, parameterized by assumptions.
-/

/-- Threshold Unforgeability under Chosen Message Attack.
    Adversary can't forge signatures without ≥ threshold honest parties.

    Proof sketch (informal):
    1. Assume adversary A forges with advantage ε
    2. Build SIS solver B that uses A as subroutine
    3. B embeds SIS challenge into public key
    4. When A outputs forgery (m*, σ*), B extracts SIS solution
    5. By SIS hardness, ε must be negligible -/
def thresholdUFcma (S : Scheme) (A : Assumptions S) : Prop :=
  A.hashRO ∧ A.commitCR ∧ A.normLeakageBound

/-- Key secrecy: adversary learns nothing about secret shares.

    Proof sketch (informal):
    1. Public key pk = A·sk where sk is secret
    2. If adversary distinguishes sk from random, solve MLWE
    3. By MLWE hardness, pk reveals nothing about sk -/
def keySecrecy (S : Scheme) (A : LatticeAssumptions S) : Prop :=
  MLWEHard A.mlweInst

/-- Liveness for bounded local rejection sampling: the abort probability after
`cfg.maxLocalAttempts` attempts is explicitly bounded.

This is a purely probabilistic statement about the idealized loop model (`localRejectionDist`).
Connecting it to the `IO` implementation is deferred.
-/
theorem livenessOrAbort
    {S : Scheme} [NormBounded S.Secret]
    {cfg : ThresholdConfig}
    {nonceDist : DistFamily (S.Secret × S.Secret)}
    {expectedIterations : Nat}
    (h : AcceptanceRateBound S cfg nonceDist expectedIterations)
    (bindingFactor : S.Scalar) (c : S.Challenge) (s : S.Secret) (κ : Nat) :
    Dist.prob (localRejectionDist S cfg nonceDist bindingFactor c s κ) {none}
      ≤ (((expectedIterations - 1 : Nat) : ENNReal) / (expectedIterations : ENNReal)) ^ cfg.maxLocalAttempts := by
  simpa using (AcceptanceRateBound.failureProb_localRejectionDist_none_le
    (S := S) (cfg := cfg) (nonceDist := nonceDist) (expectedIterations := expectedIterations)
    h bindingFactor c s κ)

/-!
## Parameter Validation

Lightweight checks to catch obviously insecure or invalid parameters.
These are necessary conditions, not sufficient for security - real analysis
requires the lattice estimator tool (Albrecht et al., https://lattice-estimator.readthedocs.io/).

### SIS Security Requirements (soundness checks)

For SIS(n, m, q, β) to be hard (post-quantum):
1. n ≥ 256
2. m ≥ 2n
3. β < q/2
4. q prime or prime power

### MLWE Security Requirements (soundness checks)

For MLWE(n, k, q, η) to be hard:
1. n ≥ 256 and power of 2 (for NTT)
2. k ≥ 1 (k=1 = Ring-LWE; higher k improves security)
3. η small (typically ≤ 4)
4. q ≥ n and NTT-friendly (q ≡ 1 mod 2n)
-/

/-- Minimum dimension for 128-bit security against known lattice attacks -/
def minSecureDimension : Nat := 256

/-- SIS validation result with specific failure reason -/
inductive SISValidation
  | ok
  | dimensionTooSmall (n : Nat) (minRequired : Nat)
  | notEnoughColumns (m : Nat) (minRequired : Nat)
  | betaTooLarge (beta : Nat) (maxAllowed : Nat)
  | modulusTooSmall (q : Nat)
  deriving DecidableEq, Repr

/-- Validate SIS parameters, returning specific error if invalid -/
def SISParams.validate (p : SISParams) : SISValidation :=
  if p.n < minSecureDimension then
    .dimensionTooSmall p.n minSecureDimension
  else if p.m < 2 * p.n then
    .notEnoughColumns p.m (2 * p.n)
  else if p.beta ≥ p.q / 2 then
    .betaTooLarge p.beta (p.q / 2)
  else if p.q < 2 then
    .modulusTooSmall p.q
  else
    .ok

/-- Check if SIS parameters are valid (boolean) -/
def SISParams.isValid (p : SISParams) : Bool :=
  p.validate = .ok

/-- Check if SIS parameters are secure (Prop) -/
def SISParams.isSecure (p : SISParams) : Prop :=
  p.n ≥ minSecureDimension ∧
  p.m ≥ 2 * p.n ∧
  p.beta < p.q / 2

/-- MLWE validation result with specific failure reason -/
inductive MLWEValidation
  | ok
  | ringDimensionTooSmall (n : Nat) (minRequired : Nat)
  | ringDimensionNotPowerOf2 (n : Nat)
  | moduleRankTooSmall (k : Nat)
  | errorBoundTooLarge (eta : Nat) (maxAllowed : Nat)
  | modulusTooSmall (q : Nat)
  deriving DecidableEq, Repr

/-- Check if n is a power of 2 -/
def isPowerOf2 (n : Nat) : Bool :=
  n > 0 && (n &&& (n - 1)) = 0

/-- Validate MLWE parameters, returning specific error if invalid -/
def MLWEParams.validate (p : MLWEParams) : MLWEValidation :=
  if p.n < minSecureDimension then
    .ringDimensionTooSmall p.n minSecureDimension
  else if !isPowerOf2 p.n then
    .ringDimensionNotPowerOf2 p.n
  else if p.k < 1 then
    .moduleRankTooSmall p.k
  else if p.eta > 4 then
    .errorBoundTooLarge p.eta 4
  else if p.q < p.n then
    .modulusTooSmall p.q
  else
    .ok

/-- Check if MLWE parameters are valid (boolean) -/
def MLWEParams.isValid (p : MLWEParams) : Bool :=
  p.validate = .ok

/-- Check if MLWE parameters are secure (Prop) -/
def MLWEParams.isSecure (p : MLWEParams) : Prop :=
  p.n ≥ minSecureDimension ∧
  p.k ≥ 1 ∧
  p.eta ≤ 4

-- Security-bit estimates are not computed here; use external lattice-estimator.
def SISParams.estimatedSecurityBits (_p : SISParams) : Option Nat := none
def MLWEParams.estimatedSecurityBits (_p : MLWEParams) : Option Nat := none

/-!
## Dilithium Signing Parameters

Following Green's analysis, Dilithium requires careful parameter tuning for:
1. Rejection sampling to work (γ₁ > β where β = τ·η)
2. HighBits consistency (γ₂ > β to absorb error term c·s₂)
3. Security against lattice attacks

**Reference**: Green, "To Schnorr and Beyond, Part 2", 2023.
https://blog.cryptographyengineering.com/2023/11/30/to-schnorr-and-beyond-part-2/
-/

/-- Dilithium signing parameters.

    These parameters control the rejection sampling and HighBits truncation
    that make Dilithium secure. Green's blog post explains:

    - **τ (tau)**: Challenge weight - number of ±1 coefficients in challenge c
    - **η (eta)**: Secret coefficient bound - ||s₁||∞, ||s₂||∞ ≤ η
    - **γ₁ (gamma1)**: Nonce coefficient range - ||y||∞ < γ₁
    - **γ₂ (gamma2)**: HighBits truncation - absorbs error term c·s₂
    - **β = τ·η**: Maximum magnitude of c·s (since ||c||₁ ≤ τ, ||s||∞ ≤ η)

    The key constraints are:
    1. γ₁ > β: Rejection sampling has room to mask c·s₁
    2. γ₂ > β: HighBits absorbs c·s₂ during verification -/
structure DilithiumSigningParams where
  /-- Ring dimension (always 256 for Dilithium) -/
  n : Nat := 256
  /-- Modulus q = 2²³ - 2¹³ + 1 = 8380417 -/
  q : Nat := 8380417
  /-- Challenge weight: number of ±1 coefficients in c -/
  tau : Nat
  /-- Secret coefficient bound: ||s₁||∞, ||s₂||∞ ≤ η -/
  eta : Nat
  /-- Nonce coefficient range: ||y||∞ < γ₁ -/
  gamma1 : Nat
  /-- HighBits truncation parameter -/
  gamma2 : Nat
  /-- Module dimensions (k×l matrix A) -/
  k : Nat
  l : Nat
  deriving Repr

/-- Compute β = τ·η, the bound on ||c·s||∞ -/
def DilithiumSigningParams.beta (p : DilithiumSigningParams) : Nat :=
  p.tau * p.eta

/-- Compute the rejection bound: γ₁ - β -/
def DilithiumSigningParams.zBound (p : DilithiumSigningParams) : Nat :=
  p.gamma1 - p.beta

/-- Validation errors for Dilithium signing parameters -/
inductive DilithiumValidation
  | ok
  | gamma1TooSmall (gamma1 beta : Nat)  -- γ₁ ≤ β means no room for rejection
  | gamma2TooSmall (gamma2 beta : Nat)  -- γ₂ ≤ β means HighBits fails
  | tauTooLarge (tau : Nat)             -- Challenge weight too high
  | etaTooLarge (eta : Nat)             -- Secret bound too high
  | invalidDimensions (k l : Nat)       -- Module dimensions invalid
  deriving DecidableEq, Repr

/-- Validate Dilithium signing parameters.

    From Green's post, the two critical constraints are:
    1. γ₁ > β: "sufficiently large compared to" c·s₁
    2. γ₂ > β: HighBits absorbs the error term -/
def DilithiumSigningParams.validate (p : DilithiumSigningParams) : DilithiumValidation :=
  let beta := p.beta
  if p.gamma1 ≤ beta then
    .gamma1TooSmall p.gamma1 beta
  else if p.gamma2 ≤ beta then
    .gamma2TooSmall p.gamma2 beta
  else if p.tau > 60 then  -- Dilithium max is 60
    .tauTooLarge p.tau
  else if p.eta > 4 then   -- Dilithium max is 4
    .etaTooLarge p.eta
  else if p.k < 1 || p.l < 1 then
    .invalidDimensions p.k p.l
  else
    .ok

/-- Check if Dilithium parameters are valid -/
def DilithiumSigningParams.isValid (p : DilithiumSigningParams) : Bool :=
  p.validate = .ok

/-- Security predicate for Dilithium parameters -/
def DilithiumSigningParams.isSecure (p : DilithiumSigningParams) : Prop :=
  p.gamma1 > p.beta ∧
  p.gamma2 > p.beta ∧
  p.tau ≤ 60 ∧
  p.eta ≤ 4 ∧
  p.k ≥ 1 ∧
  p.l ≥ 1

/-- NIST Level 2 (Dilithium2): 128-bit security -/
def dilithiumL2 : DilithiumSigningParams :=
  { tau := 39
    eta := 2
    gamma1 := 2^17  -- 131072
    gamma2 := 95232 -- (q-1)/88
    k := 4
    l := 4 }

/-- NIST Level 3 (Dilithium3): 192-bit security -/
def dilithiumL3 : DilithiumSigningParams :=
  { tau := 49
    eta := 4
    gamma1 := 2^19  -- 524288
    gamma2 := 261888 -- (q-1)/32
    k := 6
    l := 5 }

/-- NIST Level 5 (Dilithium5): 256-bit security -/
def dilithiumL5 : DilithiumSigningParams :=
  { tau := 60
    eta := 2
    gamma1 := 2^19  -- 524288
    gamma2 := 261888 -- (q-1)/32
    k := 8
    l := 7 }

/-- Validate standard parameter sets -/
theorem dilithiumL2_valid : dilithiumL2.isValid = true := by native_decide
theorem dilithiumL3_valid : dilithiumL3.isValid = true := by native_decide
theorem dilithiumL5_valid : dilithiumL5.isValid = true := by native_decide

/-- Verify γ₁ > β for Level 2 -/
theorem dilithiumL2_gamma1_ok : dilithiumL2.gamma1 > dilithiumL2.beta := by
  native_decide

/-- Verify γ₂ > β for Level 2 -/
theorem dilithiumL2_gamma2_ok : dilithiumL2.gamma2 > dilithiumL2.beta := by
  native_decide

/-- Expected signing iterations: approximately γ₁ / (γ₁ - β).
    For Dilithium2: 131072 / (131072 - 78) ≈ 1.0006, so ~1 attempt on average.
    The blog post mentions 4-7 iterations; this is for the full protocol
    including both quality checks. -/
def DilithiumSigningParams.expectedIterations (p : DilithiumSigningParams) : Nat :=
  if p.gamma1 > p.beta then
    -- Approximate: γ₁ / (γ₁ - β), rounded up
    (p.gamma1 + p.gamma1 - p.beta - 1) / (p.gamma1 - p.beta)
  else
    0  -- Invalid parameters

/-- Dilithium2 expects roughly 1 iteration per attempt -/
example : dilithiumL2.expectedIterations = 2 := by native_decide

/-- Combined Dilithium configuration linking signing params to SIS/MLWE -/
structure DilithiumConfig where
  signing : DilithiumSigningParams
  sis : SISParams
  mlwe : MLWEParams
  /-- Signing params are valid -/
  signing_valid : signing.isValid = true
  /-- SIS params are valid -/
  sis_valid : sis.isValid = true
  /-- MLWE params are valid -/
  mlwe_valid : mlwe.isValid = true

/-- Validate that our concrete NIST-aligned parameter sets are valid -/
theorem sisL1_valid : sisL1.isValid = true := by native_decide
theorem sisL3_valid : sisL3.isValid = true := by native_decide
theorem sisL5_valid : sisL5.isValid = true := by native_decide
theorem mlweL1_valid : mlweL1.isValid = true := by native_decide
theorem mlweL3_valid : mlweL3.isValid = true := by native_decide
theorem mlweL5_valid : mlweL5.isValid = true := by native_decide

/-- Level 2 configuration -/
def dilithiumConfigL2 : DilithiumConfig :=
  { signing := dilithiumL2
    sis := sisL1
    mlwe := mlweL1
    signing_valid := dilithiumL2_valid
    sis_valid := sisL1_valid
    mlwe_valid := mlweL1_valid }

/-- Level 3 configuration -/
def dilithiumConfigL3 : DilithiumConfig :=
  { signing := dilithiumL3
    sis := sisL3
    mlwe := mlweL3
    signing_valid := dilithiumL3_valid
    sis_valid := sisL3_valid
    mlwe_valid := mlweL3_valid }

/-- Level 5 configuration -/
def dilithiumConfigL5 : DilithiumConfig :=
  { signing := dilithiumL5
    sis := sisL5
    mlwe := mlweL5
    signing_valid := dilithiumL5_valid
    sis_valid := sisL5_valid
    mlwe_valid := mlweL5_valid }

/-- Combined validation for a full lattice assumption set -/
def LatticeAssumptions.validate {S : Scheme} (A : LatticeAssumptions S) : Bool :=
  A.sisInst.isValid && A.mlweInst.isValid

/-- Human-readable security summary (bit estimates external). -/
structure SecuritySummary where
  sisValid : Bool
  mlweValid : Bool
  sisSecurityBits : Option Nat
  mlweSecurityBits : Option Nat
  overallSecurityBits : Option Nat  -- min if both available
  deriving Repr

/-- Generate security summary for lattice assumptions -/
def LatticeAssumptions.securitySummary {S : Scheme} (A : LatticeAssumptions S) : SecuritySummary :=
  let sisBits := A.sisInst.estimatedSecurityBits
  let mlweBits := A.mlweInst.estimatedSecurityBits
  { sisValid := A.sisInst.isValid
    mlweValid := A.mlweInst.isValid
    sisSecurityBits := sisBits
    mlweSecurityBits := mlweBits
    overallSecurityBits := do
      let s ← sisBits
      let m ← mlweBits
      return min s m }

/-!
## Axiom Index

This section documents all axioms used throughout the codebase for easy reference.
Axioms are kept in their respective modules for locality but indexed here.

### Protocol Axioms

| Axiom | Module | Purpose |
|-------|--------|---------|
-- Lagrange coefficient properties are now proven in `Protocol/Core/Lagrange`
| `List.sum_perm` | Protocol/RefreshCoord | Permuted lists have equal sums |
| `Finset.ofList_toList_perm` | Protocol/RefreshCoord | Finset conversion preserves elements |
| `MsgMap.merge_senders_comm` | Protocol/Phase | Message map merge is commutative |
| `MsgMap.merge_idem` | Protocol/Phase | Message map merge is idempotent |

### Security Axioms

| Axiom | Module | Purpose |
|-------|--------|---------|
| `vss_correctness` | Proofs/Soundness/VSS | Honest shares verify against commitments |
| `vss_soundness` | Proofs/Soundness/VSS | Invalid shares are detected |
| `vss_hiding` | Proofs/Soundness/VSS | Commitments hide polynomial coefficients |
| `reconstruction_unique` | Proofs/Soundness/VSS | Unique polynomial from sufficient shares |
| `refresh_privacy` | Proofs/Extensions/Coordination | Refresh masks hide original shares |
| `repair_privacy` | Proofs/Extensions/Coordination | Repair contributions hide helper shares |
| `dilithium_acceptance_probability` | Proofs/Correctness/Correctness | Rejection sampling acceptance rate |

### Justifications

All axioms fall into three categories:

1. **Mathlib-equivalent**: Properties that should be provable with Mathlib but
   require significant integration work (e.g., `coeffs_sum_to_one`).

2. **Cryptographic assumptions**: Properties that cannot be proven from first
   principles and require computational hardness assumptions (e.g., `vss_hiding`).

3. **Implementation details**: Properties about data structures that would require
   extensive formalization (e.g., `MsgMap.merge_idem`).

**References**:
- Lagrange interpolation: Burden & Faires, "Numerical Analysis", Ch. 3
- VSS: Feldman, "A Practical Scheme for Non-interactive Verifiable Secret Sharing", FOCS 1987
- Rejection sampling: Lyubashevsky, "Fiat-Shamir with Aborts", ASIACRYPT 2009
-/

end IceNine.Proofs
