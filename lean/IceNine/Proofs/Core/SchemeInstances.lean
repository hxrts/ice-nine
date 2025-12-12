/-
# Scheme Typeclass Instance Helpers

Helpers for resolving algebraic typeclass ambiguity when working with Scheme.

## The Problem

The `Scheme` record bundles typeclass instances like `scalarSemiring`, `secretModule`,
etc. However, when proofs also have instances like `[Field S.Scalar]` in scope,
Lean may encounter ambiguity:

- `S.scalarSemiring : Semiring S.Scalar` (from Scheme)
- `Field S.Scalar` implies `Semiring S.Scalar` (from Mathlib)

This can cause typeclass resolution to fail or pick the wrong instance.

## The Solution

Use `letI` to explicitly select the scheme's instances. This module provides:

1. **Section macros**: `useSchemeInstances` installs all scheme instances at once
2. **Documentation**: Examples and best practices for handling ambiguity
3. **Wrapper lemmas**: Versions of Mathlib lemmas specialized to scheme instances

## Usage

```lean
theorem my_theorem (S : Scheme) [Field S.Scalar] ... := by
  -- Install scheme instances to resolve ambiguity
  letI := S.scalarSemiring
  letI := S.secretModule
  -- Now proofs using Module S.Scalar S.Secret will use the scheme's instance
  ...
```

Or use the provided section pattern:

```lean
section SchemeProofs
variable (S : Scheme) [Field S.Scalar]

-- Set scheme instances for this section
attribute [local instance] Scheme.scalarSemiring Scheme.secretModule

theorem my_theorem ... := by
  ...

end SchemeProofs
```

## Best Practices

1. **Always use scheme instances in proofs**: When working with `S.Secret`, `S.Public`,
   use `S.secretModule`, `S.publicModule` rather than relying on inference.

2. **Be explicit at lemma boundaries**: When calling lemmas that use algebraic
   typeclasses, ensure the instances match.

3. **Prefer letI over haveI**: `letI` creates a definition (more predictable),
   while `haveI` creates a local hypothesis.

4. **Document when needed**: If a proof needs explicit instance selection,
   add a comment explaining why.
-/

import IceNine.Protocol.Core.Core
import Mathlib

set_option autoImplicit false

namespace IceNine.Proofs.Core.SchemeInstances

open IceNine.Protocol

/-!
## Instance Selection Helpers

These helpers explicitly bind scheme instances to avoid ambiguity.
-/

/-- Install scheme's Semiring instance for Scalar.
    Use when Field S.Scalar is also in scope. -/
@[inline] def withScalarSemiring (S : Scheme) {α : Sort*}
    (f : @Semiring S.Scalar S.scalarSemiring → α) : α :=
  f S.scalarSemiring

/-- Install scheme's Module instance for Secret.
    Use when multiple Module instances might be inferred. -/
@[inline] def withSecretModule (S : Scheme) {α : Sort*}
    (f : @Module S.Scalar S.Secret S.scalarSemiring S.secretAdd.toAddCommMonoid S.secretModule → α) : α :=
  f S.secretModule

/-- Install scheme's Module instance for Public.
    Use when multiple Module instances might be inferred. -/
@[inline] def withPublicModule (S : Scheme) {α : Sort*}
    (f : @Module S.Scalar S.Public S.scalarSemiring S.publicAdd.toAddCommMonoid S.publicModule → α) : α :=
  f S.publicModule

/-!
## Common Patterns

Examples of how to handle typeclass ambiguity in proofs.
-/

section Examples

variable (S : Scheme) [Field S.Scalar]

/-- Example: scalar multiplication on secrets using scheme instance.
    The letI pattern explicitly selects the scheme's module structure. -/
example (c : S.Scalar) (s : S.Secret) : S.Secret := by
  letI : Semiring S.Scalar := S.scalarSemiring
  letI : Module S.Scalar S.Secret := S.secretModule
  exact c • s

/-- Example: sum of secrets using scheme's additive structure.
    The letI pattern ensures AddCommGroup comes from the scheme. -/
example (ss : List S.Secret) : S.Secret := by
  letI : AddCommGroup S.Secret := S.secretAdd
  exact ss.sum

/-- Example: linear map application preserves scheme structure.
    No letI needed since A's type already constrains the instances. -/
example (s : S.Secret) : S.Public :=
  S.A s

end Examples

/-!
## Lemma Wrappers

These wrap common Mathlib lemmas with explicit scheme instance constraints.
Use these to avoid ambiguity when the standard versions cause issues.
-/

/-- smul_add specialized to scheme's secret module -/
theorem scheme_smul_add_secret (S : Scheme) (c : S.Scalar) (s1 s2 : S.Secret) :
    @HSMul.hSMul S.Scalar S.Secret S.Secret
      (@instHSMul S.Scalar S.Secret S.secretModule.toSMul) c (s1 + s2) =
    @HSMul.hSMul S.Scalar S.Secret S.Secret
      (@instHSMul S.Scalar S.Secret S.secretModule.toSMul) c s1 +
    @HSMul.hSMul S.Scalar S.Secret S.Secret
      (@instHSMul S.Scalar S.Secret S.secretModule.toSMul) c s2 := by
  letI : Semiring S.Scalar := S.scalarSemiring
  letI : AddCommGroup S.Secret := S.secretAdd
  letI : Module S.Scalar S.Secret := S.secretModule
  exact smul_add c s1 s2

/-- add_smul specialized to scheme's secret module -/
theorem scheme_add_smul_secret (S : Scheme) (c1 c2 : S.Scalar) (s : S.Secret) :
    @HSMul.hSMul S.Scalar S.Secret S.Secret
      (@instHSMul S.Scalar S.Secret S.secretModule.toSMul) (c1 + c2) s =
    @HSMul.hSMul S.Scalar S.Secret S.Secret
      (@instHSMul S.Scalar S.Secret S.secretModule.toSMul) c1 s +
    @HSMul.hSMul S.Scalar S.Secret S.Secret
      (@instHSMul S.Scalar S.Secret S.secretModule.toSMul) c2 s := by
  letI : Semiring S.Scalar := S.scalarSemiring
  letI : AddCommGroup S.Secret := S.secretAdd
  letI : Module S.Scalar S.Secret := S.secretModule
  exact add_smul c1 c2 s

/-- LinearMap.map_add specialized to scheme's linear map A -/
theorem scheme_A_map_add (S : Scheme) (s1 s2 : S.Secret) :
    S.A (s1 + s2) = S.A s1 + S.A s2 :=
  map_add S.A s1 s2

/-- LinearMap.map_smul specialized to scheme's linear map A -/
theorem scheme_A_map_smul (S : Scheme) (c : S.Scalar) (s : S.Secret) :
    S.A (c • s) = c • S.A s :=
  LinearMap.map_smul S.A c s

/-- Sum distributes through A -/
theorem scheme_A_sum (S : Scheme) (ss : List S.Secret) :
    S.A ss.sum = (ss.map S.A).sum := by
  induction ss with
  | nil => simp [map_zero]
  | cons s ss ih =>
    simp only [List.sum_cons, map_add, List.map_cons]
    rw [ih]

/-!
## Tactic Helpers

Macros for common instance-binding patterns.
-/

/-- Install all standard scheme instances in the current goal.
    Use at the start of proofs involving scheme algebra. -/
macro "install_scheme_instances" S:ident : tactic =>
  `(tactic|
    (letI : Semiring $S.Scalar := $S.scalarSemiring
     letI : AddCommGroup $S.Secret := $S.secretAdd
     letI : AddCommGroup $S.Public := $S.publicAdd
     letI : Module $S.Scalar $S.Secret := $S.secretModule
     letI : Module $S.Scalar $S.Public := $S.publicModule))

end IceNine.Proofs.Core.SchemeInstances
