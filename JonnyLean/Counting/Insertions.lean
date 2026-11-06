import JonnyLean.Counting.Dependent
namespace JonnyLean.Counting

def insertions (a : α) : List α → List (List α)
  | [] => [[a]]
  | b :: xs => (a :: b :: xs) :: (insertions a xs).map (fun ys => b :: ys)

theorem length_insertions (a : α) (xs : List α) : (insertions a xs).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [insertions, ih]

theorem insertion_length (a : α) {xs ys : List α} (h : ys ∈ insertions a xs) : ys.length = xs.length + 1 := by
  induction xs generalizing ys with
  | nil => have : ys = [a] := by simpa [insertions] using h
           subst ys; rfl
  | cons b xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · rfl
    · obtain ⟨zs, hz, rfl⟩ := List.mem_map.mp h
      simp [ih hz]

theorem insertion_contains (a : α) {xs ys : List α} (h : ys ∈ insertions a xs) : a ∈ ys := by
  induction xs generalizing ys with
  | nil => have : ys = [a] := by simpa [insertions] using h
           subst ys; exact List.mem_cons_self
  | cons b xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · obtain ⟨zs, hz, rfl⟩ := List.mem_map.mp h
      exact List.mem_cons_of_mem b (ih hz)

theorem insert_front (a : α) (xs : List α) : a :: xs ∈ insertions a xs := by
  cases xs <;> exact List.mem_cons_self
end JonnyLean.Counting
