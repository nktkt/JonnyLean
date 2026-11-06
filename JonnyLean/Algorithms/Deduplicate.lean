import Std
import JonnyLean.FiniteSet.Basic

namespace JonnyLean.Algorithms

/-- Keep the final occurrence of each value, preserving their original order. -/
def deduplicate [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then deduplicate xs else x :: deduplicate xs

theorem mem_deduplicate [DecidableEq α] (x : α) (xs : List α) :
    x ∈ deduplicate xs ↔ x ∈ xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [deduplicate]
    split
    next ha =>
      rw [ih, List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun hxa => hxa ▸ ha) id⟩
    next => simp only [List.mem_cons, ih]

theorem deduplicate_nodup [DecidableEq α] (xs : List α) : (deduplicate xs).Nodup := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    simp only [deduplicate]
    split
    · exact ih
    next hx => exact List.nodup_cons.mpr ⟨fun h => hx ((mem_deduplicate x xs).mp h), ih⟩

theorem deduplicate_length_le [DecidableEq α] (xs : List α) :
    (deduplicate xs).length ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [deduplicate, List.length_cons]
    split
    · exact Nat.le_trans ih (Nat.le_succ _)
    · simpa only [List.length_cons] using Nat.succ_le_succ ih

theorem deduplicate_of_nodup [DecidableEq α] (xs : List α) (h : xs.Nodup) :
    deduplicate xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp h
    simp only [deduplicate, if_neg hx, ih hxs]

theorem deduplicate_idempotent [DecidableEq α] (xs : List α) :
    deduplicate (deduplicate xs) = deduplicate xs :=
  deduplicate_of_nodup _ (deduplicate_nodup xs)

def toFiniteSet [DecidableEq α] (xs : List α) : FiniteSet α :=
  ⟨deduplicate xs, deduplicate_nodup xs⟩

theorem mem_toFiniteSet [DecidableEq α] (x : α) (xs : List α) :
    x ∈ toFiniteSet xs ↔ x ∈ xs := mem_deduplicate x xs

end JonnyLean.Algorithms
