import JonnyLean.Algorithms.FirstMatch

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-045. -/
theorem JL045 {α : Type u} (p : α → Bool) (xs : List α) :
    xs = (JonnyLean.Algorithms.firstMatchSplit p xs).1 ++
      (JonnyLean.Algorithms.firstMatchSplit p xs).2 ∧
    (∀ x ∈ (JonnyLean.Algorithms.firstMatchSplit p xs).1, p x = false) ∧
    (∀ x tail, (JonnyLean.Algorithms.firstMatchSplit p xs).2 = x :: tail → p x = true) :=
  JonnyLean.Algorithms.firstMatchSplit_certificate p xs

example : JonnyLean.Algorithms.firstMatchSplit (fun n : Nat => n == 2) [1, 3, 2, 2] =
    ([1, 3], [2, 2]) := by decide

example : JonnyLean.Algorithms.firstMatchSplit (fun n : Nat => n == 7) [1, 3, 2] =
    ([1, 3, 2], []) := by decide

example {α : Type u} (p : α → Bool) :
    JonnyLean.Algorithms.firstMatchSplit p ([] : List α) = ([], []) := rfl
end JonnyLean.Contracts

#print axioms JonnyLean.Algorithms.firstMatchSplit_certificate
#print axioms JonnyLean.Contracts.JL045
