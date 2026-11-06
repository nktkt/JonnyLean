import Std

namespace JonnyLean.Algorithms

def orderedInsert (r : α → α → Prop) [DecidableRel r] (a : α) : List α → List α
  | [] => [a]
  | b :: xs => if r a b then a :: b :: xs else b :: orderedInsert r a xs

def insertionSort (r : α → α → Prop) [DecidableRel r] : List α → List α
  | [] => []
  | a :: xs => orderedInsert r a (insertionSort r xs)

theorem orderedInsert_perm (r : α → α → Prop) [DecidableRel r] (a : α) (xs : List α) :
    (orderedInsert r a xs).Perm (a :: xs) := by
  induction xs with
  | nil => exact .refl _
  | cons b xs ih =>
    simp only [orderedInsert]
    split
    · exact .refl _
    · exact (ih.cons b).trans (List.Perm.swap _ _ _)

theorem orderedInsert_mem (r : α → α → Prop) [DecidableRel r] (a x : α) (xs : List α) :
    x ∈ orderedInsert r a xs ↔ x = a ∨ x ∈ xs := by
  rw [(orderedInsert_perm r a xs).mem_iff, List.mem_cons]

theorem insertionSort_perm (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    (insertionSort r xs).Perm xs := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih => exact (orderedInsert_perm r a _).trans (ih.cons a)

theorem insertionSort_length (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    (insertionSort r xs).length = xs.length := (insertionSort_perm r xs).length_eq

theorem insertionSort_mem (r : α → α → Prop) [DecidableRel r] (x : α) (xs : List α) :
    x ∈ insertionSort r xs ↔ x ∈ xs := (insertionSort_perm r xs).mem_iff

end JonnyLean.Algorithms
