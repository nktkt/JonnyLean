import JonnyLean.Counting.Dependent
namespace JonnyLean.Counting

def splits : List α → List (List α × List α)
  | [] => [([], [])]
  | a :: xs => ([], a :: xs) :: (splits xs).map (fun p => (a :: p.1, p.2))

theorem length_splits (xs : List α) : (splits xs).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [splits, ih]

theorem mem_splits {xs u v : List α} : (u, v) ∈ splits xs ↔ u ++ v = xs := by
  induction xs generalizing u v with
  | nil => simp [splits]
  | cons a xs ih =>
    cases u with
    | nil => simp [splits]
    | cons b u =>
      constructor
      · intro h
        rcases List.mem_cons.mp h with h | h
        · cases h
        · obtain ⟨⟨p, q⟩, hm, he⟩ := List.mem_map.mp h
          cases he
          exact congrArg (List.cons a) (ih.mp hm)
      · intro h
        have he := List.cons.inj h
        rcases he with ⟨rfl, he⟩
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(u, v), ih.mpr he, rfl⟩)

theorem splits_left (xs : List α) : ([], xs) ∈ splits xs := mem_splits.mpr rfl

theorem splits_right (xs : List α) : (xs, []) ∈ splits xs := mem_splits.mpr (List.append_nil _)
end JonnyLean.Counting
