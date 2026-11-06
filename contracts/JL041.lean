import JonnyLean.Algorithms.InsertionSort

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-041. -/
theorem JL041 {α : Type u} (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    (JonnyLean.Algorithms.insertionSort r xs).Perm xs :=
  JonnyLean.Algorithms.insertionSort_perm r xs

example : JonnyLean.Algorithms.insertionSort (fun a b : Nat => a ≤ b) [3, 1, 2, 1] =
    [1, 1, 2, 3] := by decide

example {α : Type u} (r : α → α → Prop) [DecidableRel r] :
    JonnyLean.Algorithms.insertionSort r [] = [] := rfl
end JonnyLean.Contracts

#print axioms JonnyLean.Algorithms.insertionSort_perm
#print axioms JonnyLean.Contracts.JL041
