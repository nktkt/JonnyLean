import JonnyLean.Algorithms.InsertionSort

namespace JonnyLean.Algorithms

theorem orderedInsert_sorted (r : α → α → Prop) [DecidableRel r]
    (total : ∀ a b, r a b ∨ r b a)
    (trans : ∀ a b c, r a b → r b c → r a c)
    (a : α) (xs : List α) (hs : xs.Pairwise r) : (orderedInsert r a xs).Pairwise r := by
  induction xs with
  | nil => simp [orderedInsert]
  | cons b xs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    simp only [orderedInsert]
    split
    next hab =>
      apply List.pairwise_cons.mpr
      refine ⟨?_, List.pairwise_cons.mpr ⟨hhead, htail⟩⟩
      intro x hx
      cases List.mem_cons.mp hx with
      | inl hxb => exact hxb ▸ hab
      | inr hx => exact trans a b x hab (hhead x hx)
    next hab =>
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih htail⟩
      intro x hx
      cases (orderedInsert_mem r a x xs).mp hx with
      | inl hxa => exact hxa ▸ (total a b).resolve_left hab
      | inr hx => exact hhead x hx

theorem insertionSort_sorted (r : α → α → Prop) [DecidableRel r]
    (total : ∀ a b, r a b ∨ r b a)
    (trans : ∀ a b c, r a b → r b c → r a c) (xs : List α) :
    (insertionSort r xs).Pairwise r := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih => exact orderedInsert_sorted r total trans a _ ih

theorem orderedInsert_of_lower_bound (r : α → α → Prop) [DecidableRel r]
    (a : α) (xs : List α) (h : ∀ b ∈ xs, r a b) : orderedInsert r a xs = a :: xs := by
  cases xs with
  | nil => rfl
  | cons b xs => simp [orderedInsert, h b List.mem_cons_self]

theorem insertionSort_of_sorted (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (hs : xs.Pairwise r) : insertionSort r xs = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    simp only [insertionSort, ih htail]
    exact orderedInsert_of_lower_bound r a xs hhead

theorem insertionSort_idempotent (r : α → α → Prop) [DecidableRel r]
    (total : ∀ a b, r a b ∨ r b a)
    (trans : ∀ a b c, r a b → r b c → r a c) (xs : List α) :
    insertionSort r (insertionSort r xs) = insertionSort r xs :=
  insertionSort_of_sorted r _ (insertionSort_sorted r total trans xs)

end JonnyLean.Algorithms
