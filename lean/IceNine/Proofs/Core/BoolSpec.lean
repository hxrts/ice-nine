/-
# Bool↔Prop Reflection Lemmas

Standardized reflection lemmas connecting Boolean runtime checks to Prop specifications.
These follow the naming convention `foo_spec : foo = true ↔ FooProp`.

## Usage

Import this module to get access to reflection lemmas for:
- VSS verification
- Zero-sum verification
- HashMap/MsgMap membership
- Signature validation

Each lemma connects a Bool-returning function to its propositional specification.
-/

import Mathlib
import IceNine.Protocol.Core.Core
import IceNine.Protocol.DKG.VSSDKG
import IceNine.Protocol.Shares.RefreshCoord

set_option autoImplicit false

namespace IceNine.Proofs.Core.BoolSpec

open IceNine.Protocol

/-!
## General Boolean Reflection

Standard lemmas for working with Boolean predicates.
-/

/-- beq reflection: a == b = true ↔ a = b -/
theorem beq_spec {α : Type*} [BEq α] [LawfulBEq α] (a b : α) :
    (a == b) = true ↔ a = b := beq_iff_eq

/-- beq_false reflection: a == b = false ↔ a ≠ b -/
theorem beq_false_spec {α : Type*} [BEq α] [LawfulBEq α] (a b : α) :
    (a == b) = false ↔ a ≠ b := beq_eq_false_iff_ne _ _

/-- decide reflection: decide p = true ↔ p -/
theorem decide_spec (p : Prop) [Decidable p] :
    decide p = true ↔ p := decide_eq_true_iff p

/-- decide_false reflection: decide p = false ↔ ¬p -/
theorem decide_false_spec (p : Prop) [Decidable p] :
    decide p = false ↔ ¬p := decide_eq_false_iff_not p

/-!
## Option Reflection

Lemmas for Option predicates.
-/

/-- Option.isSome reflection -/
theorem Option.isSome_spec {α : Type*} (o : Option α) :
    o.isSome = true ↔ ∃ a, o = some a := Option.isSome_iff_exists

/-- Option.isNone reflection -/
theorem Option.isNone_spec {α : Type*} (o : Option α) :
    o.isNone = true ↔ o = none := by
  cases o <;> simp

/-!
## VSS Verification Reflection

Lemmas connecting VSS Boolean checks to propositional specifications.
-/

/-- VSS share verification: verifyShareBool = true ↔ verifyShare -/
theorem VSS.verifyShareBool_spec
    (S : Scheme) [CommRing S.Scalar] [AddCommGroup S.Public] [Module S.Scalar S.Public] [DecidableEq S.Public]
    (comm : VSS.PolyCommitment S) (share : VSS.VSSShare S) :
    VSS.verifyShareBool S comm share = true ↔ VSS.verifyShare S comm share := by
  simp [VSS.verifyShareBool]

/-- VSS complaint verification: verifyComplaint = true ↔ ¬verifyShare -/
theorem VSS.verifyComplaint_spec
    (S : Scheme) [CommRing S.Scalar] [AddCommGroup S.Public] [Module S.Scalar S.Public] [DecidableEq S.Public]
    (complaint : VSS.VSSComplaint S) :
    VSS.verifyComplaint S complaint = true ↔ ¬VSS.verifyShare S complaint.commitment complaint.badShare := by
  simp [VSS.verifyComplaint, VSS.verifyShareBool]

/-!
## Refresh Coordination Reflection

Lemmas for refresh protocol verification.
-/

/-- Zero-sum verification reflection -/
theorem RefreshCoord.verifyZeroSum_spec
    (S : Scheme)
    (st : RefreshCoord.RefreshState S) :
    RefreshCoord.verifyZeroSum S st = true ↔ RefreshCoord.zeroSumProp S st := by
  simp only [RefreshCoord.verifyZeroSum, RefreshCoord.zeroSumProp]
  exact decide_eq_true_iff _

/-!
## List Membership Reflection

Lemmas for list operations.
-/

/-- List.elem reflection (for BEq types) -/
theorem List.elem_spec {α : Type*} [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    l.elem a = true ↔ a ∈ l := List.elem_iff

/-- List.contains reflection -/
theorem List.contains_spec {α : Type*} [BEq α] [LawfulBEq α] (l : List α) (a : α) :
    l.contains a = true ↔ a ∈ l := List.contains_iff

/-!
## Signature Validation Reflection

Lemmas for signature verification.
-/

/-- Signature verification with nonce: verifyWithNonce = true ↔ verification equation holds -/
theorem Sign.verifyWithNonce_spec
    (S : Scheme)
    (pk : S.Public)
    (sig : Signature S)
    (w : S.Public) :
    verifyWithNonce S pk sig w = true ↔ S.A sig.z = w + sig.c • pk := by
  simp only [verifyWithNonce, decide_eq_true_iff]

end IceNine.Proofs.Core.BoolSpec
