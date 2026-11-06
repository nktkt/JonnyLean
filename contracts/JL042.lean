import JonnyLean.Algorithms.SortCorrectness

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-042. -/
theorem JL042 {α : Type u} (r : α → α → Prop) [DecidableRel r]
    (total : ∀ a b, r a b ∨ r b a)
    (trans : ∀ a b c, r a b → r b c → r a c) (xs : List α) :
    (JonnyLean.Algorithms.insertionSort r xs).Pairwise r :=
  JonnyLean.Algorithms.insertionSort_sorted r total trans xs

example {α : Type u} (r : α → α → Prop) [DecidableRel r]
    (total : ∀ a b, r a b ∨ r b a)
    (trans : ∀ a b c, r a b → r b c → r a c) (xs : List α) :
    JonnyLean.Algorithms.insertionSort r (JonnyLean.Algorithms.insertionSort r xs) =
      JonnyLean.Algorithms.insertionSort r xs :=
  JonnyLean.Algorithms.insertionSort_idempotent r total trans xs
end JonnyLean.Contracts

#print axioms JonnyLean.Algorithms.insertionSort_sorted
#print axioms JonnyLean.Contracts.JL042
