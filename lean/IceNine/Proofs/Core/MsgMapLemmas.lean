/-
# MsgMap and HashMap Reasoning Lemmas

Centralized lemmas for reasoning about Std.HashMap and MsgMap keyset membership.
These lemmas avoid re-deriving ad-hoc facts about contains/toList membership,
union properties, and fold operations.

## Contents

- HashMap membership reflection (contains ↔ mem)
- HashMap operation lemmas (insert, contains, fold)
- MsgMap-specific lemmas (senders, merge, monotonicity)

## Usage

Import this module to get access to centralized HashMap/MsgMap reasoning.
Prefer using these lemmas over deriving similar facts inline.

## Unordered ⇒ Set-Level Statement Convention

For HashMap-backed collections like MsgMap, **avoid list-equality facts**
for properties that are inherently unordered. Instead:

1. **Prefer `Finset`/`Set` equalities**: Use `.toFinset` for set-level statements
   - Good: `(a ⊔ b).senders.toFinset = a.senders.toFinset ∪ b.senders.toFinset`
   - Avoid: `(a ⊔ b).senders = ...` (list equality depends on iteration order)

2. **Use `List.Perm` when bridging**: If you need to convert between list and
   set operations (e.g., for sum invariance), use `List.Perm` to express that
   the lists contain the same elements.

3. **Exception**: List equality is acceptable for the empty case (`senders = []`)
   since there's no ordering ambiguity.

This convention ensures proofs don't depend on HashMap iteration order,
which is an implementation detail.

## Re-exports

This module re-exports key lemmas from Extensions.Phase for convenience:
- `MsgMap.senders_merge`: merge preserves union of sender sets
- `MsgMap.merge_senders_comm`: sender sets commutative under merge
- `MsgMap.merge_idem`: merge is idempotent
-/

import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas
import IceNine.Protocol.Core.CRDT
import Mathlib

set_option autoImplicit false

namespace IceNine.Proofs.Core.MsgMapLemmas

open IceNine.Protocol
open Std

/-!
## HashMap Membership Reflection

Lemmas connecting HashMap operations to propositional statements.
-/

/-- HashMap.contains reflection: contains = true ↔ key ∈ map -/
theorem HashMap.contains_spec {K V : Type*} [BEq K] [Hashable K] [EquivBEq K] [LawfulHashable K]
    (m : HashMap K V) (k : K) :
    m.contains k = true ↔ k ∈ m :=
  HashMap.contains_iff_mem

/-- HashMap.contains via isSome: contains = isSome of getElem? -/
theorem HashMap.contains_eq_isSome {K V : Type*} [BEq K] [Hashable K] [EquivBEq K] [LawfulHashable K]
    (m : HashMap K V) (k : K) :
    m.contains k = m[k]?.isSome :=
  HashMap.contains_eq_isSome_getElem? (m := m) (a := k)

/-- HashMap membership via getElem?: k ∈ m ↔ ∃ v, m[k]? = some v -/
theorem HashMap.mem_iff_getElem?_some {K V : Type*} [BEq K] [Hashable K] [EquivBEq K] [LawfulHashable K]
    (m : HashMap K V) (k : K) :
    k ∈ m ↔ ∃ v, m[k]? = some v := by
  constructor
  · intro hk
    have hisSome : m[k]?.isSome = true := by
      rwa [← HashMap.contains_eq_isSome_getElem?, HashMap.contains_iff_mem]
    exact Option.isSome_iff_exists.mp hisSome
  · intro ⟨v, hv⟩
    rw [HashMap.contains_iff_mem]
    have hisSome : m[k]?.isSome = true := by simp [hv]
    rwa [HashMap.contains_eq_isSome_getElem?]

/-!
## HashMap Insert Lemmas

Lemmas for reasoning about HashMap.insert.
-/

/-- HashMap.insert preserves contains for existing keys -/
theorem HashMap.contains_insert_of_contains {K V : Type*}
    [BEq K] [Hashable K] [EquivBEq K] [LawfulHashable K]
    (m : HashMap K V) (k k' : K) (v : V)
    (hk : m.contains k = true) :
    (m.insert k' v).contains k = true := by
  rw [HashMap.contains_insert]
  simp [hk]

/-- HashMap.insert adds the inserted key -/
theorem HashMap.contains_insert_same {K V : Type*}
    [BEq K] [Hashable K] [EquivBEq K] [LawfulHashable K]
    (m : HashMap K V) (k : K) (v : V) :
    (m.insert k v).contains k = true := by
  rw [HashMap.contains_insert]
  simp

/-- HashMap.insert for different key: contains unchanged when k' ≠ k -/
theorem HashMap.contains_insert_ne {K V : Type*}
    [BEq K] [Hashable K] [EquivBEq K] [LawfulHashable K]
    (m : HashMap K V) (k k' : K) (v : V)
    (hne : (k' == k) = false) :
    (m.insert k' v).contains k = m.contains k := by
  rw [HashMap.contains_insert]
  simp [hne]

/-!
## HashMap toList Membership

Lemmas connecting toList membership to HashMap operations.
-/

/-- toList membership ↔ getElem? = some -/
theorem HashMap.mem_toList_iff_getElem?_some {K V : Type*}
    [BEq K] [Hashable K] [EquivBEq K] [LawfulHashable K]
    (m : HashMap K V) (k : K) (v : V) :
    (k, v) ∈ m.toList ↔ m[k]? = some v :=
  HashMap.mem_toList_iff_getElem?_eq_some

/-- Key in toList.map Prod.fst ↔ key in map -/
theorem HashMap.mem_toList_keys_iff_mem {K V : Type*}
    [BEq K] [Hashable K] [EquivBEq K] [LawfulHashable K]
    (m : HashMap K V) (k : K) :
    k ∈ m.toList.map Prod.fst ↔ k ∈ m := by
  constructor
  · intro hk
    rcases List.mem_map.mp hk with ⟨⟨k', v⟩, hkv, hfst⟩
    simp at hfst
    have : (k', v) ∈ m.toList := hkv
    have hget : m[k']? = some v := (HashMap.mem_toList_iff_getElem?_eq_some).mp this
    have hmem : k' ∈ m := (HashMap.mem_iff_getElem?_some m k').mpr ⟨v, hget⟩
    rw [← hfst]
    exact hmem
  · intro hk
    rcases (HashMap.mem_iff_getElem?_some m k).mp hk with ⟨v, hv⟩
    have hmem : (k, v) ∈ m.toList := (HashMap.mem_toList_iff_getElem?_eq_some).mpr hv
    exact List.mem_map.mpr ⟨(k, v), hmem, rfl⟩

/-!
## HashMap Fold Lemmas

Lemmas for reasoning about HashMap.fold operations.
-/

/-- HashMap.fold equals foldl over toList -/
theorem HashMap.fold_eq_foldl {K V A : Type*}
    [BEq K] [Hashable K]
    (m : HashMap K V) (f : A → K → V → A) (init : A) :
    m.fold f init = m.toList.foldl (fun acc kv => f acc kv.1 kv.2) init :=
  HashMap.fold_eq_foldl_toList

/-- Folding over HashMap with no-op step is identity -/
theorem HashMap.fold_noop_eq_init {K V : Type*}
    [BEq K] [Hashable K] [EquivBEq K] [LawfulHashable K]
    (m : HashMap K V)
    (init : HashMap K V)
    (hall : ∀ kv ∈ m.toList, init.contains kv.1 = true) :
    m.fold (fun acc k v => if acc.contains k then acc else acc.insert k v) init = init := by
  rw [HashMap.fold_eq_foldl_toList]
  generalize hl : m.toList = l at hall
  induction l generalizing init with
  | nil => simp
  | cons kv tl ih =>
    simp only [List.foldl_cons]
    have hkv : init.contains kv.1 = true := hall kv (List.mem_cons_self kv tl)
    simp only [hkv, ↓reduceIte]
    exact ih init (fun x hx => hall x (List.mem_cons_of_mem kv hx))

/-!
## MsgMap Membership Lemmas

Lemmas connecting MsgMap operations to sender set membership.
-/

/-- MsgMap.senders membership ↔ MsgMap.map contains -/
theorem MsgMap.mem_senders_iff_contains {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    (m : MsgMap S M) (k : S.PartyId) :
    k ∈ m.senders ↔ m.map.contains k = true := by
  simp only [MsgMap.senders]
  constructor
  · intro hk
    rcases List.mem_map.mp hk with ⟨⟨k', v⟩, hkv, hfst⟩
    simp at hfst
    have : (k', v) ∈ m.map.toList := hkv
    have hget : m.map[k']? = some v := (HashMap.mem_toList_iff_getElem?_eq_some).mp this
    have hisSome : m.map[k']?.isSome = true := by simp [hget]
    rw [← hfst]
    rwa [HashMap.contains_eq_isSome_getElem?]
  · intro hk
    have hisSome : m.map[k]?.isSome = true := by
      rwa [← HashMap.contains_eq_isSome_getElem?]
    rcases Option.isSome_iff_exists.mp hisSome with ⟨v, hv⟩
    have hmem : (k, v) ∈ m.map.toList := (HashMap.mem_toList_iff_getElem?_eq_some).mpr hv
    have : k ∈ List.map Prod.fst m.map.toList := List.mem_map.mpr ⟨(k, v), hmem, rfl⟩
    exact this

/-- MsgMap.senders.toFinset membership ↔ contains (requires DecidableEq) -/
theorem MsgMap.mem_senders_toFinset_iff_contains {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    [EquivBEq S.PartyId] [LawfulHashable S.PartyId] [LawfulBEq S.PartyId]
    (m : MsgMap S M) (k : S.PartyId) :
    k ∈ m.senders.toFinset ↔ m.map.contains k = true := by
  rw [List.mem_toFinset]
  exact MsgMap.mem_senders_iff_contains m k

/-- MsgMap.contains reflection -/
theorem MsgMap.contains_spec {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    [LawfulBEq S.PartyId]
    (m : MsgMap S M) (k : S.PartyId) :
    m.contains k = true ↔ k ∈ m.senders := by
  simp only [MsgMap.contains]
  exact (MsgMap.mem_senders_iff_contains m k).symm

/-!
## MsgMap Insert Monotonicity

Lemmas for reasoning about MsgMap.insert preserving ordering.
-/

/-- MsgMap.insert is monotone with respect to key-set inclusion -/
theorem MsgMap.insert_monotone {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    [LawfulBEq S.PartyId]
    (getSender : M → S.PartyId) (msg : M)
    (a b : MsgMap S M) (hab : a ≤ b) :
    MsgMap.insert getSender a msg ≤ MsgMap.insert getSender b msg := by
  intro k hk
  classical
  let sender : S.PartyId := getSender msg
  unfold MsgMap.insert at hk ⊢
  by_cases hbSender : b.map.contains sender = true
  · rw [if_pos hbSender]
    by_cases haSender : a.map.contains sender = true
    · rw [if_pos haSender] at hk
      exact hab k hk
    · rw [if_neg haSender] at hk
      rw [HashMap.contains_insert] at hk
      cases h : (sender == k) with
      | true =>
        have heq : sender = k := beq_iff_eq.mp h
        rw [← heq]
        exact hbSender
      | false =>
        simp only [h, Bool.false_or] at hk
        exact hab k hk
  · rw [if_neg hbSender]
    by_cases haSender : a.map.contains sender = true
    · have hbHas : b.map.contains sender = true := hab sender haSender
      exact absurd hbHas hbSender
    · rw [if_neg haSender] at hk
      rw [HashMap.contains_insert] at hk ⊢
      cases h : (sender == k) with
      | true => simp [h]
      | false =>
        simp only [h, Bool.false_or] at hk ⊢
        exact hab k hk

/-!
## MsgMap Size Lemmas
-/

/-- MsgMap size after insert is at most size + 1 -/
theorem MsgMap.size_insert_le {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    (getSender : M → S.PartyId) (m : MsgMap S M) (msg : M) :
    (MsgMap.insert getSender m msg).size ≤ m.size + 1 := by
  unfold MsgMap.insert MsgMap.size
  by_cases h : m.map.contains (getSender msg)
  · simp [h]
  · simp only [Bool.not_eq_true] at h
    simp only [h, ↓reduceIte]
    exact HashMap.size_insert_le

/-- MsgMap.empty has size 0 -/
theorem MsgMap.size_empty {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] :
    (MsgMap.empty : MsgMap S M).size = 0 := by
  simp [MsgMap.empty, MsgMap.size, HashMap.size_empty]

/-- MsgMap.senders of empty is empty list -/
theorem MsgMap.senders_empty {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] :
    (MsgMap.empty : MsgMap S M).senders = [] := by
  simp only [MsgMap.senders, MsgMap.empty]
  native_decide

/-- MsgMap.senders.toFinset of empty is empty finset (set-level statement) -/
theorem MsgMap.senders_toFinset_empty {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId] :
    (MsgMap.empty : MsgMap S M).senders.toFinset = ∅ := by
  simp [MsgMap.senders_empty]

/-!
## MsgMap Get/Contains Lemmas
-/

/-- MsgMap.get? some implies contains -/
theorem MsgMap.get?_some_implies_contains {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    (m : MsgMap S M) (k : S.PartyId) (v : M)
    (hget : m.get? k = some v) :
    m.contains k = true := by
  simp only [MsgMap.get?, MsgMap.contains] at hget ⊢
  rw [HashMap.contains_eq_isSome_getElem?, hget]
  rfl

/-- MsgMap.contains true implies get? is some -/
theorem MsgMap.contains_implies_get?_some {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    (m : MsgMap S M) (k : S.PartyId)
    (hcontains : m.contains k = true) :
    ∃ v, m.get? k = some v := by
  simp only [MsgMap.get?, MsgMap.contains] at hcontains ⊢
  rw [HashMap.contains_eq_isSome_getElem?] at hcontains
  exact Option.isSome_iff_exists.mp hcontains

end IceNine.Proofs.Core.MsgMapLemmas
