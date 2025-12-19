/-
# Probability Layer: Rejection Loops

The protocol implementation performs local rejection by looping until an
acceptance predicate holds, with a hard cap `maxLocalAttempts`.

We do not model `IO` directly. Instead, we model the loop's output distribution
in terms of repeated i.i.d. draws from a base distribution.

For most security arguments, the key fact is that the *unbounded* loop's output
distribution is the conditional distribution (`Dist.filter`) of a single draw
given acceptance. For liveness / negligible-failure arguments, we also need the
*truncated* loop with a maximum attempt count.
-/

import IceNine.Proofs.Probability.Lemmas

set_option autoImplicit false

namespace IceNine.Proofs.Probability

open scoped BigOperators

noncomputable section

namespace Dist

universe u

variable {α : Type u}

/-- Single attempt: sample from `d` and keep the value iff it lies in `accept`. -/
def attemptOption (d : Dist α) (accept : Set α) : Dist (Option α) := by
  classical
  exact Dist.map (fun x => if x ∈ accept then some x else none) d

/-- Sequential “try up to `n` times, return the first accepted value” loop. -/
def repeatOption (d : Dist α) (accept : Set α) : Nat → Dist (Option α)
  | 0 => Dist.pure none
  | n + 1 =>
      Dist.bind (attemptOption d accept) (fun
        | some x => Dist.pure (some x)
        | none => repeatOption d accept n)

theorem prob_attemptOption_none (d : Dist α) (accept : Set α) :
    Dist.prob (attemptOption d accept) {none} = Dist.prob d (acceptᶜ) := by
  classical
  -- Reduce to a preimage under `map`.
  simpa [attemptOption, Set.preimage, Set.compl_def] using
    (Dist.prob_map_preimage (d := d) (f := fun x => if x ∈ accept then some x else none)
      (s := ({none} : Set (Option α))))

theorem prob_repeatOption_none (d : Dist α) (accept : Set α) :
    ∀ n, Dist.prob (repeatOption d accept n) {none} = (Dist.prob d (acceptᶜ)) ^ n
  | 0 => by
      -- No attempts: always `none`.
      have hmem : (none : Option α) ∈ ({none} : Set (Option α)) := by simp
      simpa [repeatOption] using
        (Dist.prob_pure_of_mem (a := (none : Option α)) (s := ({none} : Set (Option α))) hmem)
  | n + 1 => by
      classical
      let attempt : Dist (Option α) := attemptOption d accept
      let cont : Option α → Dist (Option α) :=
        fun
          | some x => Dist.pure (some x)
          | none => repeatOption d accept n
      have hSome : ∀ x : α, Dist.prob (Dist.pure (some x)) ({none} : Set (Option α)) = 0 := by
        intro x
        refine Dist.prob_pure_of_notMem (a := some x) (s := ({none} : Set (Option α))) ?_
        simp
      have hNone : Dist.prob (repeatOption d accept n) ({none} : Set (Option α)) =
          (Dist.prob d (acceptᶜ)) ^ n := prob_repeatOption_none d accept n

      -- Start from the bind law.
      have hbind :
          Dist.prob (repeatOption d accept (n + 1)) ({none} : Set (Option α)) =
            ∑' o, attempt.toPMF o * Dist.prob (cont o) ({none} : Set (Option α)) := by
        simp [repeatOption, attempt, cont, Dist.prob_bind]

      -- Only the `none` branch can contribute.
      have hsplit :
          (∑' o, attempt.toPMF o * Dist.prob (cont o) ({none} : Set (Option α))) =
            attempt.toPMF none * Dist.prob (cont none) ({none} : Set (Option α)) := by
        -- Split off the `none` term and show all other terms are zero.
        let H : Option α → ENNReal :=
          fun o => attempt.toPMF o * Dist.prob (cont o) ({none} : Set (Option α))
        have hH_ite :
            ∀ o, @ite ENNReal (o = none) (Classical.propDecidable (o = none)) 0 (H o) = 0 := by
          intro o
          cases o with
          | none => simp [H]
          | some x =>
              have : Dist.prob (cont (some x)) ({none} : Set (Option α)) = 0 := by
                simpa [cont] using hSome x
              simp [H, this]
        calc
          (∑' o, H o) =
              H none + ∑' o, @ite ENNReal (o = none) (Classical.propDecidable (o = none)) 0 (H o) := by
            simpa using (ENNReal.tsum_eq_add_tsum_ite (f := H) (b := (none : Option α)))
          _ = H none := by simp [hH_ite]
          _ = attempt.toPMF none * Dist.prob (cont none) ({none} : Set (Option α)) := rfl

      -- Rewrite the remaining pieces.
      have hAttemptNone : attempt.toPMF none = Dist.prob d (acceptᶜ) := by
        -- `attempt.toPMF none = prob attempt {none} = prob d acceptᶜ`.
        have : Dist.prob attempt ({none} : Set (Option α)) = attempt.toPMF none := by
          simpa using (Dist.prob_singleton (d := attempt) (a := (none : Option α)))
        -- Rearrange.
        calc
          attempt.toPMF none = Dist.prob attempt ({none} : Set (Option α)) := this.symm
          _ = Dist.prob d (acceptᶜ) := by
                simpa [attempt] using (prob_attemptOption_none (d := d) (accept := accept))

      have hContNone : Dist.prob (cont none) ({none} : Set (Option α)) = (Dist.prob d (acceptᶜ)) ^ n := by
        simpa [cont] using hNone

      -- Conclude.
      calc
        Dist.prob (repeatOption d accept (n + 1)) ({none} : Set (Option α))
            = ∑' o, attempt.toPMF o * Dist.prob (cont o) ({none} : Set (Option α)) := hbind
        _ = attempt.toPMF none * Dist.prob (cont none) ({none} : Set (Option α)) := hsplit
        _ = Dist.prob d (acceptᶜ) * (Dist.prob d (acceptᶜ)) ^ n := by simp [hAttemptNone, hContNone]
        _ = (Dist.prob d (acceptᶜ)) ^ (n + 1) := by
              calc
                Dist.prob d (acceptᶜ) * (Dist.prob d (acceptᶜ)) ^ n
                    = (Dist.prob d (acceptᶜ)) ^ n * Dist.prob d (acceptᶜ) := by
                        simp [mul_comm]
                _ = (Dist.prob d (acceptᶜ)) ^ (n + 1) := by
                        simp [pow_succ]

end Dist

end

end IceNine.Proofs.Probability
