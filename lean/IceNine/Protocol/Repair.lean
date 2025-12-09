/-
# Share repair (RTS-style, sketch)

We model a simple repair protocol: a target party asks a helper set; each helper
provides a masked delta that lets the target reconstruct its share without
revealing others.
-/

import IceNine.Protocol.Core

namespace IceNine.Protocol

open List

/-- Repair message from a helper. -/
structure RepairMsg (S : Scheme) :=
  (from   : S.PartyId)
  (to     : S.PartyId)
  (delta  : S.Secret)

/--
  Combine helper deltas to repair a lost share. Assumes deltas sum to the target
  share value (in additive-sharing setting).
-/
def repairShare
  (S : Scheme)
  (msgs : List (RepairMsg S))
  : S.Secret :=
  msgs.foldl (fun acc m => acc + m.delta) (0 : S.Secret)

/-- Correctness (idealized): if deltas sum to sk_i, repairShare recovers sk_i. -/
lemma repair_correct
  (S : Scheme)
  (msgs : List (RepairMsg S))
  (sk_i : S.Secret)
  (h : msgs.foldl (fun acc m => acc + m.delta) (0 : S.Secret) = sk_i) :
  repairShare S msgs = sk_i := by
  simp [repairShare, h]

/--
  Privacy (informal): if each delta is masked with helper-local randomness that
  sums to 0, the sum reveals only sk_i. Here we capture the algebraic part: an
  additional zero-sum mask does not change the repaired value.
-/
lemma repair_masked_zero
  (S : Scheme)
  (msgs : List (RepairMsg S))
  (mask : List S.Secret)
  (hmask : mask.sum = 0)
  (hlen : mask.length = msgs.length) :
  repairShare S (List.zipWith (fun m z => { m with delta := m.delta + z }) msgs mask)
    = repairShare S msgs := by
  unfold repairShare
  revert msgs mask
  induction hlen generalizing msgs mask with
  | refl =>
      intro msgs mask
      cases msgs <;> cases mask <;> simp at hmask
      · simp
      · simp [List.foldl_map] at hmask
  | _ => simp

end IceNine.Protocol
