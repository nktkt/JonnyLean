import JonnyLean.Counting.Dependent
import JonnyLean.Combinatorics.Binomial
namespace JonnyLean.Counting

def shuffles : List α → List α → List (List α)
  | [], ys => [ys]
  | a :: xs, [] => [a :: xs]
  | a :: xs, b :: ys =>
    (shuffles xs (b :: ys)).map (fun w => a :: w) ++
    (shuffles (a :: xs) ys).map (fun w => b :: w)
termination_by xs ys => xs.length + ys.length

theorem shuffle_length {xs ys w : List α} (h : w ∈ shuffles xs ys) :
    w.length = xs.length + ys.length := by
  induction xs generalizing ys w with
  | nil => have hw : w = ys := by simpa [shuffles] using h
           subst w; simp
  | cons a xs ih =>
    induction ys generalizing w with
    | nil => have hw : w = a :: xs := by simpa [shuffles] using h
             subst w; simp
    | cons b ys jh =>
      rw [shuffles] at h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
        simp [ih hv, Nat.add_comm, Nat.add_left_comm]
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
        simp [jh hv, Nat.add_comm, Nat.add_left_comm]

theorem length_shuffles (xs ys : List α) :
    (shuffles xs ys).length = Combinatorics.binomial (xs.length + ys.length) xs.length := by
  induction xs generalizing ys with
  | nil => simp [shuffles]
  | cons a xs ih =>
    induction ys with
    | nil => simp [shuffles, Combinatorics.binomial_diagonal]
    | cons b ys jh =>
      rw [shuffles, List.length_append, List.length_map, List.length_map, ih, jh]
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Combinatorics.binomial_pascal (xs.length + ys.length + 1) xs.length).symm

theorem shuffle_empty_right (xs : List α) : shuffles xs [] = [xs] := by cases xs <;> simp [shuffles]
end JonnyLean.Counting
