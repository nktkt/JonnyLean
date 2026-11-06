import Std

namespace JonnyLean.Collections

/-- Stable, one-pass partition, with accepted elements in the first component. -/
def partition (p : α → Bool) : List α → List α × List α
  | [] => ([], [])
  | x :: xs =>
    let rest := partition p xs
    if p x then (x :: rest.1, rest.2) else (rest.1, x :: rest.2)

theorem partition_filters (p : α → Bool) (xs : List α) :
    partition p xs = (xs.filter p, xs.filter (fun x => !(p x))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [partition, ih, h]

theorem partition_perm (p : α → Bool) (xs : List α) :
    ((partition p xs).1 ++ (partition p xs).2).Perm xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    cases h : p x
    · simp only [partition, h, Bool.false_eq_true, ↓reduceIte]
      exact List.perm_middle.trans (ih.cons x)
    · simpa only [partition, h, ↓reduceIte, List.cons_append] using ih.cons x

theorem partition_lengths (p : α → Bool) (xs : List α) :
    (partition p xs).1.length + (partition p xs).2.length = xs.length := by
  simpa only [List.length_append] using (partition_perm p xs).length_eq

theorem partition_separates (p : α → Bool) (xs : List α) :
    (∀ x ∈ (partition p xs).1, p x = true) ∧
    (∀ x ∈ (partition p xs).2, p x = false) := by
  rw [partition_filters]
  constructor
  · intro x hx; exact (List.mem_filter.mp hx).2
  · intro x hx
    have h := (List.mem_filter.mp hx).2
    cases hp : p x <;> simp_all

theorem partition_disjoint (p : α → Bool) (xs : List α) :
    ∀ x, x ∈ (partition p xs).1 → x ∈ (partition p xs).2 → False := by
  intro x hl hr
  have h := partition_separates p xs
  exact Bool.noConfusion ((h.1 x hl).symm.trans (h.2 x hr))

end JonnyLean.Collections
