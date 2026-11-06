import JonnyLean.Counting.Dependent
import Init.Data.List.Sublist
namespace JonnyLean.Counting

def subsequences : List α → List (List α)
  | [] => [[]]
  | a :: xs => subsequences xs ++ (subsequences xs).map (fun ys => a :: ys)

theorem length_subsequences (xs : List α) : (subsequences xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [subsequences, ih, Nat.pow_succ, Nat.mul_two]

theorem sublist_of_mem_subsequences {xs ys : List α} (h : ys ∈ subsequences xs) : ys.Sublist xs := by
  induction xs generalizing ys with
  | nil => have : ys = [] := by simpa [subsequences] using h
           subst ys; exact .slnil
  | cons a xs ih =>
    rcases List.mem_append.mp h with h | h
    · exact (ih h).cons a
    · obtain ⟨zs, hz, rfl⟩ := List.mem_map.mp h
      exact (ih hz).cons₂ a

theorem mem_subsequences_of_sublist {xs ys : List α} (h : ys.Sublist xs) : ys ∈ subsequences xs := by
  induction h with
  | slnil => exact List.mem_cons_self
  | @cons ys xs a h ih => exact List.mem_append.mpr (.inl ih)
  | @cons₂ ys xs a h ih => exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨_, ih, rfl⟩))

theorem mem_subsequences {xs ys : List α} : ys ∈ subsequences xs ↔ ys.Sublist xs :=
  ⟨sublist_of_mem_subsequences, mem_subsequences_of_sublist⟩
end JonnyLean.Counting
