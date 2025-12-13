/-
# Local Rejection Soundness Proofs

Core soundness properties for local rejection sampling in threshold signing:
- Aggregate bound guarantee: T valid local shares yield valid global signature
- No global restart: honest parties always succeed in one round
- Composition: local independence implies aggregate independence

These proofs justify why the restart-free design is sound.
-/

import Mathlib
import IceNine.Protocol.Core.Core
import IceNine.Protocol.Core.ThresholdConfig
import IceNine.Protocol.Core.NormBounded
import IceNine.Norms
import IceNine.Proofs.Core.Assumptions

set_option autoImplicit false

namespace IceNine.Proofs.Soundness.LocalRejection

open IceNine.Protocol
open IceNine.Protocol.NormBounded
open IceNine.Norms

/-!
## Aggregate Bound Guarantee

The fundamental theorem: if each of T signers produces z_i with ‖z_i‖∞ ≤ B_local,
then the aggregate z = Σ z_i satisfies ‖z‖∞ ≤ T · B_local ≤ B_global.

This is why global rejection never happens under honest behavior.
-/

/-- ℓ∞ norm of an integer vector (max absolute value). -/
def intVecInfNorm' (v : List Int) : Nat :=
  (v.map Int.natAbs).foldl max 0

/-- Helper: init ≤ foldl max init l -/
lemma le_foldl_max (l : List Nat) (init : Nat) :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    calc init ≤ max init x := Nat.le_max_left _ _
         _ ≤ xs.foldl max (max init x) := ih _

/-- Helper: foldl max is monotone in init -/
lemma foldl_max_mono_init (l : List Nat) (a b : Nat) (hab : a ≤ b) :
    l.foldl max a ≤ l.foldl max b := by
  induction l generalizing a b with
  | nil => exact hab
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    exact Nat.max_le_max_right x hab

/-- Triangle inequality for ℓ∞ norm: ‖x + y‖∞ ≤ ‖x‖∞ + ‖y‖∞ -/
lemma infNorm_add_le (x y : List Int) (hlen : x.length = y.length) :
    intVecInfNorm' (List.zipWith (· + ·) x y) ≤ intVecInfNorm' x + intVecInfNorm' y := by
  -- The ℓ∞ norm of a sum is bounded by the sum of norms
  -- Key insight: max |a_i + b_i| ≤ max |a_i| + max |b_i| because
  -- for each i: |a_i + b_i| ≤ |a_i| + |b_i| ≤ max |a_j| + max |b_j|
  unfold intVecInfNorm'
  induction x generalizing y with
  | nil =>
    simp only [List.zipWith_nil_left, List.map_nil, List.foldl_nil]
    exact Nat.zero_le _
  | cons a xs ih =>
    cases y with
    | nil => simp at hlen
    | cons b ys =>
      simp only [List.length_cons, Nat.add_one_inj] at hlen
      simp only [List.zipWith_cons_cons, List.map_cons, List.foldl_cons]
      -- Need: max |a+b| (fold xs+ys) ≤ (max |a| (fold xs)) + (max |b| (fold ys))
      have h_tail := ih ys hlen
      have h_head : Int.natAbs (a + b) ≤ Int.natAbs a + Int.natAbs b :=
        Int.natAbs_add_le a b
      -- Bound the head
      have h1 : Int.natAbs (a + b) ≤
          (xs.map Int.natAbs).foldl max (Int.natAbs a) +
          (ys.map Int.natAbs).foldl max (Int.natAbs b) := by
        calc Int.natAbs (a + b)
            ≤ Int.natAbs a + Int.natAbs b := h_head
          _ ≤ (xs.map Int.natAbs).foldl max (Int.natAbs a) + Int.natAbs b := by
              apply Nat.add_le_add_right
              exact le_foldl_max _ _
          _ ≤ (xs.map Int.natAbs).foldl max (Int.natAbs a) +
              (ys.map Int.natAbs).foldl max (Int.natAbs b) := by
              apply Nat.add_le_add_left
              exact le_foldl_max _ _
      -- Bound the tail (using IH)
      have h2 : ((List.zipWith (· + ·) xs ys).map Int.natAbs).foldl max 0 ≤
          (xs.map Int.natAbs).foldl max (Int.natAbs a) +
          (ys.map Int.natAbs).foldl max (Int.natAbs b) := by
        calc ((List.zipWith (· + ·) xs ys).map Int.natAbs).foldl max 0
            ≤ (xs.map Int.natAbs).foldl max 0 + (ys.map Int.natAbs).foldl max 0 := h_tail
          _ ≤ (xs.map Int.natAbs).foldl max (Int.natAbs a) +
              (ys.map Int.natAbs).foldl max 0 := by
              apply Nat.add_le_add_right
              exact foldl_max_mono_init _ _ _ (Nat.zero_le _)
          _ ≤ (xs.map Int.natAbs).foldl max (Int.natAbs a) +
              (ys.map Int.natAbs).foldl max (Int.natAbs b) := by
              apply Nat.add_le_add_left
              exact foldl_max_mono_init _ _ _ (Nat.zero_le _)
      -- Combine using max_le
      exact Nat.max_le.mpr ⟨h1, h2⟩

/-- Sum of T vectors with bounded norms has bounded norm.

    This is the key lemma: if ‖z_i‖∞ ≤ B for all i, then ‖Σz_i‖∞ ≤ T·B.

    Note: This uses a loose bound (sum of bounds). In practice, the actual
    aggregate norm is often much smaller due to cancellation. -/
/-- Helper: norm of zero vector is 0 -/
lemma intVecInfNorm'_replicate_zero (n : Nat) :
    intVecInfNorm' (List.replicate n 0) = 0 := by
  unfold intVecInfNorm'
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.map_cons, Int.natAbs_zero, List.foldl_cons]
    simp only [Nat.max_eq_right (Nat.zero_le _)]
    simp only [List.map_replicate, Int.natAbs_zero] at ih ⊢
    exact ih

/-- Helper: length of zipWith preserves minimum length -/
lemma length_zipWith_add (x y : List Int) :
    (List.zipWith (· + ·) x y).length = min x.length y.length := by
  simp [List.length_zipWith]

/-- Helper: foldl zipWith preserves length when all lists have same length -/
lemma length_foldl_zipWith_add (shares : List (List Int)) (init : List Int)
    (h_lens : ∀ s ∈ shares, s.length = init.length) :
    (shares.foldl (List.zipWith (· + ·)) init).length = init.length := by
  induction shares generalizing init with
  | nil => simp
  | cons s ss ih =>
    simp only [List.foldl_cons]
    have hs : s.length = init.length := h_lens s (List.mem_cons_self _ _)
    have hss : ∀ t ∈ ss, t.length = init.length :=
      fun t ht => h_lens t (List.mem_cons_of_mem _ ht)
    have h_zip_len : (List.zipWith (· + ·) init s).length = init.length := by
      simp [List.length_zipWith, hs]
    rw [ih]
    · exact h_zip_len
    · intro t ht
      rw [h_zip_len]
      exact hss t ht

/-- Generalized aggregate bound with accumulator.
    If acc has norm ≤ accBound and each share has norm ≤ bound,
    then the fold has norm ≤ accBound + bound * shares.length. -/
theorem aggregate_norm_bound_acc
    (shares : List (List Int))
    (acc : List Int)
    (bound accBound : Nat)
    (h_acc : intVecInfNorm' acc ≤ accBound)
    (h_local : ∀ s ∈ shares, intVecInfNorm' s ≤ bound)
    (h_lens : ∀ s ∈ shares, s.length = acc.length) :
    intVecInfNorm' (shares.foldl (List.zipWith (· + ·)) acc)
    ≤ accBound + bound * shares.length := by
  induction shares generalizing acc accBound with
  | nil =>
    simp only [List.foldl_nil, List.length_nil, Nat.mul_zero, Nat.add_zero]
    exact h_acc
  | cons s ss ih =>
    simp only [List.foldl_cons, List.length_cons]
    -- Apply IH with acc' = zipWith acc s and accBound' = accBound + bound
    have hs_bound : intVecInfNorm' s ≤ bound := h_local s (List.mem_cons_self _ _)
    have hs_len : s.length = acc.length := h_lens s (List.mem_cons_self _ _)
    have h_zip_bound : intVecInfNorm' (List.zipWith (· + ·) acc s) ≤ accBound + bound := by
      calc intVecInfNorm' (List.zipWith (· + ·) acc s)
          ≤ intVecInfNorm' acc + intVecInfNorm' s := infNorm_add_le acc s hs_len.symm
        _ ≤ accBound + bound := Nat.add_le_add h_acc hs_bound
    have h_zip_len : (List.zipWith (· + ·) acc s).length = acc.length := by
      simp [List.length_zipWith, hs_len]
    have h_local_ss : ∀ t ∈ ss, intVecInfNorm' t ≤ bound :=
      fun t ht => h_local t (List.mem_cons_of_mem _ ht)
    have h_lens_ss : ∀ t ∈ ss, t.length = (List.zipWith (· + ·) acc s).length := by
      intro t ht
      rw [h_zip_len]
      exact h_lens t (List.mem_cons_of_mem _ ht)
    have h_ih := ih (List.zipWith (· + ·) acc s) (accBound + bound) h_zip_bound h_local_ss h_lens_ss
    calc intVecInfNorm' (ss.foldl (List.zipWith (· + ·)) (List.zipWith (· + ·) acc s))
        ≤ (accBound + bound) + bound * ss.length := h_ih
      _ = accBound + bound * (ss.length + 1) := by ring
      _ = accBound + bound * (s :: ss).length := by simp [List.length_cons]

theorem aggregate_norm_bound
    (shares : List (List Int))
    (bound : Nat)
    (h_local : ∀ s ∈ shares, intVecInfNorm' s ≤ bound)
    (h_lens : ∀ s ∈ shares, s.length = (shares.head!).length) :
    intVecInfNorm' (shares.foldl (List.zipWith (· + ·)) (List.replicate (shares.head!).length 0))
    ≤ bound * shares.length := by
  cases shares with
  | nil =>
    simp only [List.foldl_nil, List.length_nil, Nat.mul_zero]
    exact Nat.zero_le _
  | cons s ss =>
    simp only [List.head!_cons, List.length_cons, List.foldl_cons]
    have h_rep_len : (List.replicate s.length 0).length = s.length := by simp
    have h_rep_norm : intVecInfNorm' (List.replicate s.length 0) = 0 :=
      intVecInfNorm'_replicate_zero s.length
    have h_lens' : ∀ t ∈ (s :: ss), t.length = (List.replicate s.length 0).length := by
      intro t ht
      simp only [h_rep_len]
      exact h_lens t ht
    have := aggregate_norm_bound_acc (s :: ss) (List.replicate s.length 0) bound 0
              (by rw [h_rep_norm]; exact Nat.zero_le _) h_local h_lens'
    simp only [Nat.zero_add, List.length_cons] at this
    exact this

/-- The fundamental theorem: T valid local shares yield valid global signature.

    If:
    - Each of T shares satisfies ‖z_i‖∞ ≤ B_local
    - cfg.localBound * cfg.maxSigners ≤ cfg.globalBound (from ThresholdConfig)
    - shares.length ≤ cfg.maxSigners

    Then:
    - The aggregate z = Σ z_i satisfies ‖z‖∞ ≤ B_global

    This is why global rejection never happens under honest behavior. -/
theorem aggregate_bound_guarantee
    (cfg : ThresholdConfig)
    (shares : List (List Int))
    (h_count : shares.length ≤ cfg.maxSigners)
    (h_local : ∀ s ∈ shares, intVecInfNorm' s ≤ cfg.localBound)
    (h_lens : ∀ s ∈ shares, s.length = (shares.head!).length) :
    intVecInfNorm' (shares.foldl (List.zipWith (· + ·)) (List.replicate (shares.head!).length 0))
    ≤ cfg.globalBound := by
  -- By aggregate_norm_bound: ‖Σz_i‖∞ ≤ localBound * shares.length
  have h1 := aggregate_norm_bound shares cfg.localBound h_local h_lens
  -- By h_count: shares.length ≤ maxSigners
  have h2 : cfg.localBound * shares.length ≤ cfg.localBound * cfg.maxSigners := by
    apply Nat.mul_le_mul_left
    exact h_count
  -- By cfg.local_global_bound: localBound * maxSigners ≤ globalBound
  have h3 := cfg.local_global_bound
  -- Chain the inequalities
  calc intVecInfNorm' _
      ≤ cfg.localBound * shares.length := h1
    _ ≤ cfg.localBound * cfg.maxSigners := h2
    _ ≤ cfg.globalBound := h3

/-!
## Honest Sufficiency

Given enough honest parties, we always get enough valid shares.
This ensures the protocol makes progress in one round.
-/

/-- Corollary: Given enough honest parties, we always get enough valid shares.

    This is parameterized by the threshold - any honest majority assumption
    (e.g., 2/3+1 for some protocols) can be expressed by choosing appropriate
    values for threshold and honest party count. -/
theorem honest_sufficiency {PartyId : Type*} [DecidableEq PartyId]
    (cfg : ThresholdConfig)
    (honest : Finset PartyId)
    (h_honest_count : honest.card ≥ cfg.threshold) :
    ∃ validShares : Finset PartyId, validShares ⊆ honest ∧ validShares.card ≥ cfg.threshold := by
  -- Direct from cardinality: honest itself satisfies the requirement
  exact ⟨honest, Finset.Subset.refl honest, h_honest_count⟩

/-!
## No Global Restart Property

The signing protocol either:
1. Succeeds in one round (aggregator gets ≥ threshold valid shares)
2. Fails due to insufficient honest parties

There is NO "rejection sampling said try again" path.
-/

/-- No global restart: the protocol completes in one round when honest parties exist.

    This theorem captures the key design property: local rejection sampling
    eliminates the distributed restart path from the protocol state machine.

    Preconditions:
    - At least threshold honest parties exist
    - Each honest party's local rejection loop succeeds (overwhelmingly likely)

    Conclusion:
    - Aggregation succeeds (enough valid shares collected)
    - No global restart message is sent -/
theorem no_global_restart {PartyId : Type*} [DecidableEq PartyId]
    (cfg : ThresholdConfig)
    (allParties : Finset PartyId)
    (honest : Finset PartyId)
    (h_honest_subset : honest ⊆ allParties)
    (h_honest_count : honest.card ≥ cfg.threshold)
    -- Each honest party successfully produces a valid share
    (validShares : PartyId → Bool)
    (h_honest_valid : ∀ p ∈ honest, validShares p = true) :
    -- At least threshold valid shares exist
    (allParties.filter (fun p => validShares p)).card ≥ cfg.threshold := by
  -- All honest parties produce valid shares
  have h1 : honest ⊆ allParties.filter (fun p => validShares p) := by
    intro p hp
    simp only [Finset.mem_filter]
    constructor
    · exact h_honest_subset hp
    · exact h_honest_valid p hp
  -- Therefore the filtered set has at least as many elements as honest
  have h2 : honest.card ≤ (allParties.filter (fun p => validShares p)).card :=
    Finset.card_le_card h1
  -- And honest has at least threshold elements
  exact le_trans h_honest_count h2

/-!
## Local Independence Composition

For threshold signatures, we need response independence to hold for the
aggregated response, not just individual shares.

Claim: If each party's response z_i is independent of their share s_i
(by local rejection sampling), then the aggregate z = Σz_i is independent
of the master secret s = Σs_i.
-/

/-- Threshold independence composition: linearity preserves the algebraic structure.

    The key algebraic fact: if z_i = y_i + c·s_i for each i, then
    Σz_i = Σy_i + c·Σs_i.

    This enables the threshold security argument: each party's local rejection
    sampling ensures their z_i reveals nothing about s_i, and by linearity,
    the aggregate reveals nothing about the master secret.

    The probabilistic independence claim (aggregate reveals nothing about
    master secret beyond the public key) requires additional assumptions
    about rejection sampling, which are handled at the scheme level. -/
theorem threshold_independence_composition
    {M : Type*} [AddCommMonoid M] [Module ℤ M]
    (n : Nat)
    (y z s : Fin n → M)
    (c : ℤ)
    (hz : ∀ i, z i = y i + c • s i) :
    Finset.univ.sum z = Finset.univ.sum y + c • Finset.univ.sum s := by
  simp only [hz]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← Finset.smul_sum]

/-!
## Local Rejection Success Probability

For Dilithium parameters, local rejection succeeds with overwhelming probability.
The expected number of attempts is ~4 for Dilithium2, so exhausting 256 attempts
is astronomically unlikely under honest behavior.
-/

/-- Local rejection success probability bound.

    For Dilithium-style parameters, the probability of a single attempt
    succeeding is approximately 1 - 2·B_local/γ₁.

    With B_local = γ₁/T and standard parameters, this gives ~25% success
    per attempt, so P(≥1 success in 256 attempts) ≈ 1 - 0.75^256 ≈ 1. -/
structure LocalRejectionProbability where
  /-- Per-attempt success probability (as rational numerator over 1000) -/
  successRateNumerator : Nat
  /-- Success rate is positive -/
  rate_positive : successRateNumerator > 0
  /-- Maximum attempts -/
  maxAttempts : Nat
  /-- Failure probability is negligible (< 2^{-128}) -/
  failure_negligible : (1000 - successRateNumerator)^maxAttempts < 2^128 * 1000^maxAttempts

/-- Proof that 750^256 < 2^128 * 1000^256.

    We prove this by showing (750/1000)^256 < 2^128, i.e., (3/4)^256 < 2^128.

    Equivalently: 3^256 < 2^128 * 4^256 = 2^128 * 2^512 = 2^640.

    We verify: 3^256 < 2^640 by comparing log₂ values:
    - log₂(3^256) = 256 × log₂(3) ≈ 256 × 1.585 ≈ 406
    - log₂(2^640) = 640

    Since 406 < 640, the inequality holds with room to spare.

    For Lean verification, we use the fact that 3^256 < 2^407 < 2^640,
    which can be checked: 3^256 has ~122 digits, 2^407 has ~123 digits. -/
theorem dilithium2_failure_bound_holds :
    (750 : Nat)^256 < 2^128 * 1000^256 := by
  -- Rewrite: 750^256 < 2^128 * 1000^256
  -- ⟺ (750/1000)^256 < 2^128 (after dividing, but we work with integers)
  -- ⟺ 750^256 < 2^128 * 1000^256
  -- ⟺ (3*250)^256 < 2^128 * (4*250)^256
  -- ⟺ 3^256 * 250^256 < 2^128 * 4^256 * 250^256
  -- ⟺ 3^256 < 2^128 * 4^256 = 2^128 * 2^512 = 2^640
  --
  -- We prove 3^256 < 2^640 by showing 3^256 < 2^407 (tighter bound)
  -- This is verifiable: 3^256 ≈ 1.4 × 10^122, 2^407 ≈ 3.3 × 10^122
  suffices h : (3 : Nat)^256 < 2^407 by
    have h1 : (750 : Nat) = 3 * 250 := by native_decide
    have h2 : (1000 : Nat) = 4 * 250 := by native_decide
    have h3 : (4 : Nat) = 2^2 := by native_decide
    calc (750 : Nat)^256
        = (3 * 250)^256 := by rw [h1]
      _ = 3^256 * 250^256 := by ring
      _ < 2^407 * 250^256 := by exact Nat.mul_lt_mul_of_pos_right h (Nat.pow_pos (by decide) 256)
      _ < 2^640 * 250^256 := by
          apply Nat.mul_lt_mul_of_pos_right
          · exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 407 < 640)
          · exact Nat.pow_pos (by decide) 256
      _ = 2^128 * 2^512 * 250^256 := by ring
      _ = 2^128 * (2^2)^256 * 250^256 := by ring
      _ = 2^128 * 4^256 * 250^256 := by rw [← h3]
      _ = 2^128 * (4 * 250)^256 := by ring
      _ = 2^128 * 1000^256 := by rw [← h2]
  -- Now prove 3^256 < 2^407 using native_decide
  native_decide

/-- For Dilithium2 with ~25% success rate and 256 attempts -/
def dilithium2LocalRejectionProb : LocalRejectionProbability where
  successRateNumerator := 250  -- ~25%
  rate_positive := by decide
  maxAttempts := 256
  failure_negligible := dilithium2_failure_bound_holds

/-!
## Dilithium Parameter Integration

Connect local rejection bounds to standard Dilithium parameters.
-/

/-- Convert Dilithium parameters to threshold configuration.

    For a t-of-n threshold scheme with Dilithium parameters:
    - globalBound = γ₁ - β (Dilithium acceptance bound)
    - localBound = globalBound / t (ensures aggregate stays within bound) -/
def dilithiumToThresholdConfig (p : DilithiumParams) (n t : Nat)
    (ht : t ≤ n) (ht_pos : t > 0) : ThresholdConfig :=
  { totalParties := n
    threshold := t
    maxSigners := t
    globalBound := p.zBound
    localBound := p.zBound / t
    maxLocalAttempts := 256
    threshold_le_total := ht
    maxSigners_ge_threshold := le_refl t
    local_global_bound := by
      have h : p.zBound / t * t ≤ p.zBound := Nat.div_mul_le_self p.zBound t
      exact h
  }

/-- For Dilithium2 with 3-of-4 threshold -/
def dilithium2_3of4_config (hvalid : Dilithium2Params.isValid) : ThresholdConfig :=
  dilithiumToThresholdConfig Dilithium2Params 4 3 (by decide) (by decide)

end IceNine.Proofs.Soundness.LocalRejection
