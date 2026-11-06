import JonnyLean.Counting.Insertions
import JonnyLean.NumberTheory.Factorial
namespace JonnyLean.Counting

def permutations : List α → List (List α)
  | [] => [[]]
  | a :: xs => (permutations xs).flatMap (insertions a)

theorem permutation_length {xs ys : List α} (h : ys ∈ permutations xs) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => have : ys = [] := by simpa [permutations] using h
           subst ys; rfl
  | cons a xs ih =>
    obtain ⟨zs, hz, hy⟩ := List.mem_flatMap.mp h
    rw [insertion_length a hy, ih hz, List.length_cons]

theorem mem_permutations_self (xs : List α) : xs ∈ permutations xs := by
  induction xs with
  | nil => exact List.mem_cons_self
  | cons a xs ih => exact List.mem_flatMap.mpr ⟨xs, ih, insert_front a xs⟩

theorem length_permutations (xs : List α) :
    (permutations xs).length = JonnyLean.factorial xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have h : ∀ ps : List (List α), (∀ ys, ys ∈ ps → ys.length = xs.length) →
        (ps.flatMap (insertions a)).length = ps.length * (xs.length + 1) := by
      intro ps hp
      induction ps with
      | nil => simp
      | cons ys ps hi =>
        simp only [List.flatMap_cons, List.length_append, length_insertions, List.length_cons]
        rw [hp ys List.mem_cons_self, hi (fun zs hz => hp zs (List.mem_cons_of_mem ys hz))]
        simp [Nat.add_mul, Nat.add_comm]
    change ((permutations xs).flatMap (insertions a)).length = _
    rw [h _ (fun _ => permutation_length), ih]
    simp [JonnyLean.factorial, Nat.mul_comm]
end JonnyLean.Counting
