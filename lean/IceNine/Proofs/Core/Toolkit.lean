/-
# Proof Toolkit

Reusable lemmas for common proof patterns in the Ice Nine codebase.
This module collects frequently needed plumbing lemmas for:
- Except/Option reasoning
- List.forM termination
- Monadic reasoning patterns

Import this module to avoid re-deriving these facts.
-/

import Mathlib

set_option autoImplicit false

namespace IceNine.Proofs.Core.Toolkit

/-!
## Except Reasoning

Lemmas for working with Except (error handling).
-/

/-- Except.ok preserves the value -/
theorem Except.ok_val {ε α : Type*} (a : α) :
    (Except.ok a : Except ε α).toOption = some a := rfl

/-- Except.error has no value -/
theorem Except.error_val {ε α : Type*} (e : ε) :
    (Except.error e : Except ε α).toOption = none := rfl

/-- Matching on Except.ok -/
theorem Except.ok_inj {ε α : Type*} {a b : α} :
    (Except.ok a : Except ε α) = Except.ok b ↔ a = b := by
  constructor
  · intro h; injection h
  · intro h; rw [h]

/-- Matching on Except.error -/
theorem Except.error_inj {ε α : Type*} {e1 e2 : ε} :
    (Except.error e1 : Except ε α) = Except.error e2 ↔ e1 = e2 := by
  constructor
  · intro h; injection h
  · intro h; rw [h]

/-- Ok ≠ Error -/
theorem Except.ok_ne_error {ε α : Type*} (a : α) (e : ε) :
    (Except.ok a : Except ε α) ≠ Except.error e := by
  intro h; cases h

/-- Except.isOk specification -/
theorem Except.isOk_spec {ε α : Type*} (x : Except ε α) :
    x.isOk = true ↔ ∃ a, x = Except.ok a := by
  cases x with
  | ok a => simp [Except.isOk]
  | error e => simp [Except.isOk]

/-- Except.map preserves Ok -/
theorem Except.map_ok {ε α β : Type*} (f : α → β) (a : α) :
    (Except.ok a : Except ε α).map f = Except.ok (f a) := rfl

/-- Except.map preserves Error -/
theorem Except.map_error {ε α β : Type*} (f : α → β) (e : ε) :
    (Except.error e : Except ε α).map f = Except.error e := rfl

/-!
## Option Reasoning

Lemmas for working with Option (partial values).
-/

/-- Option.bind specification for some -/
theorem Option.bind_some {α β : Type*} (a : α) (f : α → Option β) :
    (some a).bind f = f a := rfl

/-- Option.bind specification for none -/
theorem Option.bind_none {α β : Type*} (f : α → Option β) :
    (none : Option α).bind f = none := rfl

/-- Option.map specification for some -/
theorem Option.map_some' {α β : Type*} (f : α → β) (a : α) :
    (some a).map f = some (f a) := rfl

/-- Option.map specification for none -/
theorem Option.map_none' {α β : Type*} (f : α → β) :
    (none : Option α).map f = none := rfl

/-- Option.getD specification for some -/
theorem Option.getD_some {α : Type*} (a d : α) :
    (some a).getD d = a := rfl

/-- Option.getD specification for none -/
theorem Option.getD_none {α : Type*} (d : α) :
    (none : Option α).getD d = d := rfl

/-!
## List Reasoning

Lemmas for list operations and monadic traversals.
-/

/-- List.map preserves length -/
theorem List.map_length' {α β : Type*} (f : α → β) (l : List α) :
    (l.map f).length = l.length := List.length_map f l

/-- List.filterMap preserves membership (for successes) -/
theorem List.mem_filterMap_iff {α β : Type*} (f : α → Option β) (l : List α) (b : β) :
    b ∈ l.filterMap f ↔ ∃ a ∈ l, f a = some b := List.mem_filterMap

/-- List.all specification -/
theorem List.all_spec {α : Type*} (p : α → Bool) (l : List α) :
    l.all p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro ⟨hx, hall⟩
      exact ⟨hx, ih.mp hall⟩
    · intro ⟨hx, hall⟩
      exact ⟨hx, ih.mpr hall⟩

/-- List.any specification -/
theorem List.any_spec {α : Type*} (p : α → Bool) (l : List α) :
    l.any p = true ↔ ∃ a ∈ l, p a = true := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.any_cons, Bool.or_eq_true, List.mem_cons]
    constructor
    · intro h
      cases h with
      | inl hx => exact ⟨x, Or.inl rfl, hx⟩
      | inr hany =>
        obtain ⟨a, ha, hp⟩ := ih.mp hany
        exact ⟨a, Or.inr ha, hp⟩
    · intro ⟨a, hmem, hp⟩
      cases hmem with
      | inl heq => left; rw [← heq]; exact hp
      | inr hmem => right; exact ih.mpr ⟨a, hmem, hp⟩

/-!
## Finset/Set Reasoning

Lemmas connecting list and set operations.
-/

/-- List.toFinset preserves membership -/
theorem List.mem_toFinset_iff {α : Type*} [DecidableEq α] (l : List α) (a : α) :
    a ∈ l.toFinset ↔ a ∈ l := List.mem_toFinset

/-- Finset.sum over singleton -/
theorem Finset.sum_singleton' {α M : Type*} [AddCommMonoid M] [DecidableEq α]
    (a : α) (f : α → M) :
    ({a} : Finset α).sum f = f a := Finset.sum_singleton f a

/-!
## Monadic Reasoning

Lemmas for reasoning about monadic computations.
-/

/-- Pure in Id monad -/
theorem Id.pure_eq {α : Type*} (a : α) : (pure a : Id α) = a := rfl

/-- Bind in Id monad -/
theorem Id.bind_eq {α β : Type*} (a : Id α) (f : α → Id β) :
    a >>= f = f a := rfl

end IceNine.Proofs.Core.Toolkit
