import Std

namespace JonnyLean.Collections

def reverseInto : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => reverseInto xs (x :: acc)

theorem reverseInto_spec (xs acc : List α) : reverseInto xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [reverseInto, ih, List.reverse_cons, List.append_assoc]

theorem reverseInto_append (xs ys acc : List α) :
    reverseInto (xs ++ ys) acc = reverseInto ys (reverseInto xs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => exact ih (x :: acc)

theorem reverseInto_length (xs acc : List α) :
    (reverseInto xs acc).length = xs.length + acc.length := by
  rw [reverseInto_spec, List.length_append, List.length_reverse]

theorem reverseInto_map (f : α → β) (xs acc : List α) :
    (reverseInto xs acc).map f = reverseInto (xs.map f) (acc.map f) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => exact ih (x :: acc)

theorem reverseInto_involution (xs : List α) :
    reverseInto (reverseInto xs []) [] = xs := by
  simp only [reverseInto_spec, List.append_nil, List.reverse_reverse]

end JonnyLean.Collections
