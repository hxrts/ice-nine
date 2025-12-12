/-
# Phase CRDT Proofs

CRDT properties for phase state management:
1. MsgMap CRDT properties: sender commutativity, idempotence
2. Handler monotonicity: all phase handlers preserve semilattice ordering

These guarantee:
- Out-of-order message delivery doesn't break convergence
- Replaying messages is idempotent (safe in distributed setting)
- Eventual consistency: all replicas converge to same state
-/

import IceNine.Protocol.State.PhaseHandlers
import IceNine.Protocol.State.PhaseSig
import Mathlib
import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas

namespace IceNine.Proofs.Extensions.Phase

open IceNine.Protocol
open Std
open List

/-!
## MsgMap CRDT Properties

Proofs that MsgMap merge operations satisfy CRDT semilattice properties:
- Sender set union on merge
- Sender commutativity (as Finset)
- Idempotence

These are extracted from Protocol code to maintain separation of concerns.
-/

/-- Helper: senders of merge = senders of left ++ new senders from right.

    **Mathematical justification**:
    The merge operation `a ⊔ b` folds over `b.map`, adding entries whose keys
    are not already in `a.map`. Therefore the resulting senders list contains:
    - All senders from `a` (unchanged)
    - Senders from `b` that were not already in `a`

    This is exactly `a.senders ++ b.senders.filter (not in a)`.

    The list ordering depends on `Std.HashMap.toList`, so we state this as a
    *set* (Finset) equality. -/
theorem MsgMap.senders_merge (S : Scheme) {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    [LawfulBEq S.PartyId] [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    (a b : MsgMap S M) :
    (a ⊔ b).senders.toFinset = a.senders.toFinset ∪ b.senders.toFinset := by
  classical
  -- Helper: membership in `senders.toFinset` is exactly `HashMap.contains`.
  have mem_senders_toFinset_iff_contains (m : MsgMap S M) (k : S.PartyId) :
      k ∈ m.senders.toFinset ↔ m.map.contains k = true := by
    -- `senders` is `m.map.toList.map Prod.fst`.
    -- Use `Std.HashMap.mem_toList_iff_getElem?_eq_some` to shuttle between list membership and `get?`.
    constructor
    · intro hk
      have hk' : k ∈ m.senders := by
        simpa using (List.mem_toFinset.mp hk)
      rcases (List.mem_map.1 hk') with ⟨kv, hkv, hkfst⟩
      rcases kv with ⟨k', v⟩
      have hk' : k' = k := by
        simpa using hkfst
      -- `k' = k`, so the corresponding `(k, v)` is in the map's `toList`.
      have hmem : (k, v) ∈ m.map.toList := by
        simpa [hk'] using hkv
      have hget : m.map[k]? = some v := by
        simpa using
          (Std.HashMap.mem_toList_iff_getElem?_eq_some (m := m.map) (k := k) (v := v)).1 hmem
      have : m.map.contains k = (m.map[k]?.isSome) :=
        Std.HashMap.contains_eq_isSome_getElem? (m := m.map) (a := k)
      simpa [this, hget]
    · intro hk
      -- From `contains`, get a witness value via `get?`, then show the key appears in `senders`.
      have hisSome : m.map[k]?.isSome = true := by
        -- `contains` is equivalent to `isSome (get?)` for lawful hashable keys.
        simpa [Std.HashMap.contains_eq_isSome_getElem? (m := m.map) (a := k)] using hk
      rcases (Option.isSome_iff_exists.1 hisSome) with ⟨v, hv⟩
      have hmem : (k, v) ∈ m.map.toList := by
        simpa using (Std.HashMap.mem_toList_iff_getElem?_eq_some (m := m.map) (k := k) (v := v)).2 hv
      have hkSenders : k ∈ m.senders := by
        -- `k = Prod.fst (k, v)`.
        have : Prod.fst (k, v) ∈ m.map.toList.map Prod.fst :=
          List.mem_map_of_mem Prod.fst hmem
        simpa [MsgMap.senders] using this
      exact List.mem_toFinset.2 hkSenders

  -- Helper: `merge` preserves exactly the union of key sets, characterized via `contains`.
  have contains_merge (a b : MsgMap S M) (k : S.PartyId) :
      (a ⊔ b).map.contains k = (a.map.contains k || b.map.contains k) := by
    -- Unfold `merge` and rewrite `HashMap.fold` as a `foldl` over `toList`.
    classical
    let step : Std.HashMap S.PartyId M → S.PartyId → M → Std.HashMap S.PartyId M :=
      fun acc pid msg => if acc.contains pid then acc else acc.insert pid msg
    have hfold :
        b.map.fold step a.map =
          b.map.toList.foldl (fun acc kv => step acc kv.1 kv.2) a.map := by
      simpa using (Std.HashMap.fold_eq_foldl_toList (m := b.map) (f := step) (init := a.map))
    -- Reduce to the `toList.foldl` form.
    have : (b.map.fold step a.map).contains k =
        (b.map.toList.foldl (fun acc kv => step acc kv.1 kv.2) a.map).contains k := by
      simpa [hfold]
    -- Now show the `contains` result is `a.contains k || b.contains k`.
    -- Split on whether `b` contains `k`.
    by_cases hb : b.map.contains k = true
    · -- `b` contains `k`, so the merged map must contain `k`.
      have hfind_ne : b.map.toList.find? (fun kv => kv.1 == k) ≠ none := by
        intro hnone
        have hbFalse : b.map.contains k = false :=
          (Std.HashMap.find?_toList_eq_none_iff_contains_eq_false (m := b.map) (k := k)).1 hnone
        cases hbFalse.symm.trans hb
      -- Pick the first occurrence of a key `== k`.
      cases hfp : b.map.toList.find? (fun kv => kv.1 == k) with
      | none =>
          cases hfind_ne (by simpa [hfp])
      | some p =>
          -- Decompose `toList` as prefix ++ p :: suffix, with prefix not matching.
          have hpDecomp :
              (p.1 == k) = true ∧
                ∃ as bs,
                  b.map.toList = as ++ p :: bs ∧ ∀ a ∈ as, (a.1 == k) = false := by
            have h0 :=
              (List.find?_eq_some_iff_append (xs := b.map.toList) (p := fun kv => kv.1 == k) (b := p)).1 hfp
            rcases h0 with ⟨hp, as, bs, hEq, has⟩
            refine ⟨by simpa using hp, as, bs, hEq, ?_⟩
            intro a ha
            have : !(a.1 == k) = true := by
              -- `has` provides `!(p a)` as a Bool, used as Prop.
              simpa using has a ha
            -- Convert `!x = true` to `x = false`.
            cases h : (a.1 == k) <;> simp [h] at this <;> simp [h]
          rcases hpDecomp with ⟨hp, as, bs, hEq, has⟩
          -- Show folding over the prefix does not change `contains k`.
          let stepKV : Std.HashMap S.PartyId M → (S.PartyId × M) → Std.HashMap S.PartyId M :=
            fun acc kv => step acc kv.1 kv.2
          have prefix_preserves (l : List (S.PartyId × M)) (hNo : ∀ a ∈ l, (a.1 == k) = false)
              (init : Std.HashMap S.PartyId M) :
              (l.foldl stepKV init).contains k = init.contains k := by
            induction l generalizing init with
            | nil => simp
            | cons x xs ih =>
                have hx : (x.1 == k) = false := hNo x (by simp)
                have hxs : ∀ a ∈ xs, (a.1 == k) = false := by
                  intro a ha
                  exact hNo a (by simp [ha])
                -- One step: inserting a key != k doesn't affect `contains k`.
                have step_preserves :
                    (stepKV init x).contains k = init.contains k := by
                  by_cases hIn : init.contains x.1 = true
                  · simp [stepKV, step, hIn]
                  · simp [stepKV, step, hIn, Std.HashMap.contains_insert, hx]
                -- Finish by induction.
                simp [List.foldl, step_preserves, ih, hxs]
          have hPrefix :
              (as.foldl stepKV a.map).contains k = a.map.contains k :=
            prefix_preserves as has a.map
          -- After processing `p`, `contains k` becomes true, and stays true.
          have step_sets_true (init : Std.HashMap S.PartyId M) :
              (stepKV init p).contains k = true := by
            by_cases hIn : init.contains p.1 = true
            · -- `init` already contains `p.1`; since `p.1 == k`, it contains `k` as well.
              have hk' : init.contains k = true := by
                have hcongr : init.contains p.1 = init.contains k :=
                  Std.HashMap.contains_congr (m := init) (hab := hp)
                simpa [hIn] using hcongr
              simp [stepKV, step, hIn, hk']
            · -- Insert `p.1`; `p.1 == k` forces `contains k`.
              simp [stepKV, step, hIn, Std.HashMap.contains_insert, hp]
          have step_preserves_true (init : Std.HashMap S.PartyId M) (hk : init.contains k = true)
              (x : S.PartyId × M) :
              (stepKV init x).contains k = true := by
            by_cases hIn : init.contains x.1 = true
            · simp [stepKV, step, hIn, hk]
            · simp [stepKV, step, hIn, Std.HashMap.contains_insert, hk]
          -- Now combine the pieces.
          have : (b.map.toList.foldl stepKV a.map).contains k = true := by
            -- Rewrite `toList` using the decomposition.
            rw [hEq]
            -- Fold over prefix, then `p`, then suffix.
            simp [List.foldl_append, hPrefix, step_sets_true, step_preserves_true]
          -- Conclude the desired equality.
          have : (b.map.toList.foldl stepKV a.map).contains k =
              (a.map.contains k || b.map.contains k) := by
            -- RHS is `true` because `b.contains k = true`.
            simpa [this, hb]
          -- Return to the original `fold` form.
          -- First, rewrite `(a ⊔ b).map` as `b.map.fold ... a.map`.
          simpa [MsgMap.merge, Join.join, step, hfold] using this
    · -- `b` does not contain `k`, so merge preserves `a.contains k`.
      have hbFalse : b.map.contains k = false := by
        cases h : b.map.contains k <;> simp [h] at hb
        · rfl
        · cases hb (by simpa [h])
      have hfind :
          b.map.toList.find? (fun kv => kv.1 == k) = none := by
        exact (Std.HashMap.find?_toList_eq_none_iff_contains_eq_false (m := b.map) (k := k)).2 hbFalse
      have hall : ∀ x ∈ b.map.toList, (x.1 == k) = false := by
        -- `find? = none` means the predicate is false for all elements.
        have hnone : ∀ x ∈ b.map.toList, ¬ ((x.1 == k) = true) := by
          simpa [List.find?_eq_none] using hfind
        intro x hx
        cases h' : (x.1 == k) <;> simp [h'] at *
        · rfl
        · exfalso
          exact hnone x hx h'
      let stepKV : Std.HashMap S.PartyId M → (S.PartyId × M) → Std.HashMap S.PartyId M :=
        fun acc kv => step acc kv.1 kv.2
      have preserves (l : List (S.PartyId × M)) (hNo : ∀ a ∈ l, (a.1 == k) = false)
          (init : Std.HashMap S.PartyId M) :
          (l.foldl stepKV init).contains k = init.contains k := by
        induction l generalizing init with
        | nil => simp
        | cons x xs ih =>
            have hx : (x.1 == k) = false := hNo x (by simp)
            have hxs : ∀ a ∈ xs, (a.1 == k) = false := by
              intro a ha
              exact hNo a (by simp [ha])
            have step_preserves :
                (stepKV init x).contains k = init.contains k := by
              by_cases hIn : init.contains x.1 = true
              · simp [stepKV, step, hIn]
              · simp [stepKV, step, hIn, Std.HashMap.contains_insert, hx]
            simp [List.foldl, step_preserves, ih, hxs]
      have hFinal : (b.map.toList.foldl stepKV a.map).contains k = a.map.contains k :=
        preserves b.map.toList hall a.map
      -- RHS reduces to `a.contains k`.
      have : (b.map.toList.foldl stepKV a.map).contains k =
          (a.map.contains k || b.map.contains k) := by
        simpa [hFinal, hbFalse]
      simpa [MsgMap.merge, Join.join, step, hfold] using this

  ext k
  -- Reduce both sides to `contains` and use the `contains_merge` characterization.
  have hL : k ∈ (a ⊔ b).senders.toFinset ↔ (a ⊔ b).map.contains k = true :=
    mem_senders_toFinset_iff_contains (m := (a ⊔ b)) k
  have hA : k ∈ a.senders.toFinset ↔ a.map.contains k = true :=
    mem_senders_toFinset_iff_contains (m := a) k
  have hB : k ∈ b.senders.toFinset ↔ b.map.contains k = true :=
    mem_senders_toFinset_iff_contains (m := b) k
  -- `Finset` membership in a union is disjunction, and `Bool.or_eq_true` bridges to `||`.
  constructor
  · intro hk
    have hkC : (a ⊔ b).map.contains k = true := (hL.mp hk)
    have hkOr : (a.map.contains k || b.map.contains k) = true := by
      simpa [contains_merge (a := a) (b := b) (k := k)] using hkC
    have hkDisj : a.map.contains k = true ∨ b.map.contains k = true := by
      simpa using (Bool.or_eq_true_iff).1 hkOr
    rcases hkDisj with hkA | hkB
    · exact (Finset.mem_union.2 <| Or.inl (hA.2 hkA))
    · exact (Finset.mem_union.2 <| Or.inr (hB.2 hkB))
  · intro hk
    have hkDisj : k ∈ a.senders.toFinset ∨ k ∈ b.senders.toFinset := by
      simpa [Finset.mem_union] using hk
    -- We handle the disjunction explicitly.
    cases hkDisj with
    | inl ha =>
        have : a.map.contains k = true := hA.1 ha
        have hkOr : (a.map.contains k || b.map.contains k) = true := by
          simpa [this]
        have : (a ⊔ b).map.contains k = true := by
          simpa [contains_merge (a := a) (b := b) (k := k)] using hkOr
        exact hL.2 this
    | inr hb =>
        have : b.map.contains k = true := hB.1 hb
        have hkOr : (a.map.contains k || b.map.contains k) = true := by
          -- `||` with RHS true is true.
          cases ha' : a.map.contains k <;> simp [ha', this]
        have : (a ⊔ b).map.contains k = true := by
          simpa [contains_merge (a := a) (b := b) (k := k)] using hkOr
        exact hL.2 this

/-- MsgMap merge preserves the union of sender sets (as Finset).

    **Mathematical justification**:
    - `(a ⊔ b).senders` contains all senders from `a` plus senders from `b` not in `a`
    - `(b ⊔ a).senders` contains all senders from `b` plus senders from `a` not in `b`
    - As Finsets, both equal `a.senders ∪ b.senders` (set union is commutative)

    The list ordering differs between `a ⊔ b` and `b ⊔ a`, but the sender *sets*
    are identical. This is the key CRDT property: message order doesn't matter
    for determining which parties have contributed.

    This follows immediately from `MsgMap.senders_merge` and commutativity of `Finset.union`. -/
theorem MsgMap.merge_senders_comm {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    [LawfulBEq S.PartyId] [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    (a b : MsgMap S M) :
    (a ⊔ b).senders.toFinset = (b ⊔ a).senders.toFinset := by
  calc
    (a ⊔ b).senders.toFinset
        = a.senders.toFinset ∪ b.senders.toFinset := MsgMap.senders_merge (S := S) (a := a) (b := b)
    _ = b.senders.toFinset ∪ a.senders.toFinset := by
        simpa [Finset.union_comm]
    _ = (b ⊔ a).senders.toFinset := by
        symm
        simpa using (MsgMap.senders_merge (S := S) (a := b) (b := a))

/-- Helper: folding over a list where all keys are already in accumulator is identity. -/
private lemma foldl_step_noop {K V : Type*}
    [BEq K] [Hashable K] [EquivBEq K] [LawfulHashable K]
    (acc : Std.HashMap K V) (l : List (K × V))
    (h : ∀ kv ∈ l, acc.contains kv.1 = true) :
    l.foldl (fun a kv => if a.contains kv.1 then a else a.insert kv.1 kv.2) acc = acc := by
  induction l with
  | nil => simp
  | cons kv tl ih =>
      simp only [List.foldl_cons]
      have hkv : acc.contains kv.1 = true := h kv (List.mem_cons.mpr (Or.inl rfl))
      simp only [hkv, ↓reduceIte]
      exact ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

/-- MsgMap merge is idempotent.

    **Mathematical justification**:
    When merging a MsgMap with itself, we fold over `a.map` with `a.map` as the
    accumulator. For each `(k, v)` in `a.map`:
    - We check `acc.contains k`
    - Since `acc` is initially `a.map` and `k ∈ a.map`, this is always true
    - So we always take the "then" branch, returning `acc` unchanged

    Therefore `a.map.fold f a.map = a.map` and `a ⊔ a = a`.

    This is provable using `Std.HashMap.fold_eq_foldl_toList` and `Std.HashMap.mem_toList` lemmas. -/
theorem MsgMap.merge_idem {S : Scheme} {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    (a : MsgMap S M) : a ⊔ a = a := by
  classical
  cases a with
  | mk m =>
      simp only [Join.join, MsgMap.merge]
      -- Define the step function
      let step : Std.HashMap S.PartyId M → S.PartyId → M → Std.HashMap S.PartyId M :=
        fun acc pid msg => if acc.contains pid then acc else acc.insert pid msg
      -- Convert HashMap.fold to List.foldl
      have hfold : m.fold step m = m.toList.foldl (fun acc kv => step acc kv.1 kv.2) m := by
        exact Std.HashMap.fold_eq_foldl_toList (m := m) (f := step) (init := m)
      -- Show that the foldl is equal to m
      have hfoldl : m.toList.foldl (fun acc kv => step acc kv.1 kv.2) m = m := by
        apply foldl_step_noop
        intro kv hkv
        -- Membership in toList implies contains
        have : kv.1 ∈ m := Std.HashMap.mem_toList.mp hkv
        exact Std.HashMap.contains_of_mem this
      -- Combine to get the record equality
      simp only [hfold, hfoldl]

/-!
## Handler Monotonicity

Each handler function preserves the semilattice ordering.
Key property for CRDT correctness.
-/

/-- `MsgMap.insert` is monotone with respect to key-set inclusion (`≤`). -/
private lemma msgMap_insert_monotone (S : Scheme) {M : Type*}
    [BEq S.PartyId] [Hashable S.PartyId] [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    (getSender : M → S.PartyId)
    (msg : M) :
    ∀ a b : MsgMap S M, a ≤ b → MsgMap.insert getSender a msg ≤ MsgMap.insert getSender b msg := by
  intro a b hab k hk
  classical
  let sender : S.PartyId := getSender msg
  -- Unfold MsgMap.insert for both a and b
  simp only [MsgMap.insert] at hk ⊢
  by_cases hbSender : b.map.contains sender = true
  · -- `b` already contains the sender, so insertion is a no-op for `b`.
    simp only [hbSender, ↓reduceIte]
    by_cases haSender : a.map.contains sender = true
    · -- Insertion is also a no-op for `a`.
      simp only [haSender, ↓reduceIte] at hk
      exact hab k hk
    · -- `a` inserts the sender.
      simp only [haSender, Bool.false_eq_true, ↓reduceIte] at hk
      rw [Std.HashMap.contains_insert] at hk
      rcases (Bool.or_eq_true _ _).mp hk with hEq | hkA
      · -- k = sender
        have := (beq_iff_eq (a := sender) (b := k)).mp hEq
        rw [← this]
        exact hbSender
      · -- k ∈ a
        exact hab k hkA
  · -- `b` does not contain the sender, so insertion updates `b`.
    simp only [hbSender, Bool.false_eq_true, ↓reduceIte]
    by_cases haSender : a.map.contains sender = true
    · -- Impossible: `a ≤ b` would force `b` to contain the sender.
      have : b.map.contains sender = true := hab sender haSender
      simp only [this, not_true_eq_false] at hbSender
    · -- Both maps insert the sender.
      simp only [haSender, Bool.false_eq_true, ↓reduceIte] at hk
      rw [Std.HashMap.contains_insert] at hk ⊢
      rcases (Bool.or_eq_true _ _).mp hk with hEq | hkA
      · -- k = sender
        simp [hEq]
      · -- k ∈ a
        have hkB := hab k hkA
        simp [hkB]

/-- Commit handler is monotone: a ≤ b → step(a) ≤ step(b).
    Adding a commit preserves ordering between states.

    This relies on `Std.HashMap.contains_insert`/`contains_congr` to reason about key membership. -/
lemma stepCommit_monotone (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    (msg : DkgCommitMsg S) :
  ∀ a b, a ≤ b → stepCommit S msg a ≤ stepCommit S msg b := by
  intro a b hab
  simpa [stepCommit, CommitState.addCommit] using
    (msgMap_insert_monotone S (getSender := commitSender) msg a.commits b.commits hab)

/-- Reveal handler is monotone: a ≤ b → step(a) ≤ step(b).
    Adding a reveal preserves ordering between states.

    This relies on `Std.HashMap.contains_insert`/`contains_congr` to reason about key membership. -/
lemma stepReveal_monotone (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId]
    [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    (msg : DkgRevealMsg S) :
  ∀ a b, a ≤ b → stepReveal S msg a ≤ stepReveal S msg b := by
  intro a b hab
  have hcommits : a.commits ≤ b.commits := hab.1
  have hrevs : a.reveals ≤ b.reveals := hab.2
  refine And.intro hcommits ?_
  simpa [stepReveal, RevealState.addReveal] using
    (msgMap_insert_monotone S (getSender := revealSender) msg a.reveals b.reveals hrevs)

/-- Share handler is monotone on state component.
    Adding a signature share preserves ordering.

    This relies on `Std.HashMap.contains_insert`/`contains_congr` to reason about key membership. -/
lemma stepShare_monotone (S : Scheme) [BEq S.PartyId] [Hashable S.PartyId] [DecidableEq S.PartyId]
    [EquivBEq S.PartyId] [LawfulHashable S.PartyId]
    (msg : SignShareMsg S) :
  ∀ a b, a.state ≤ b.state → (stepShare S msg a).state ≤ (stepShare S msg b).state := by
  intro a b hab
  rcases hab with ⟨hcommits, hrevs, hshares, hactive⟩
  refine And.intro hcommits ?_
  refine And.intro hrevs ?_
  refine And.intro ?_ hactive
  simpa [stepShare, ShareState.addShare] using
    (msgMap_insert_monotone S (getSender := shareSender) msg a.state.shares b.state.shares hshares)

end IceNine.Proofs.Extensions.Phase
