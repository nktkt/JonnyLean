import JonnyLean.Combinatorics.Words

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.Combinatorics

theorem contract_JL055 {α : Type u} (alphabet : List α) (n : Nat) (w : List α) :
    w ∈ words alphabet n ↔ w.length = n ∧ ∀ a, a ∈ w → a ∈ alphabet := mem_words alphabet n w

example (alphabet : List α) : words alphabet 0 = [[]] := rfl
example (alphabet : List α) (n : Nat) : words alphabet (n + 1) =
    alphabet.flatMap (fun a => (words alphabet n).map (fun w => a :: w)) := rfl
example : words ([] : List Bool) 1 = [] := rfl
example : words [false, true] 2 = [[false, false], [false, true], [true, false], [true, true]] := rfl
example : words [true, true] 1 = [[true], [true]] := rfl

#print axioms JonnyLean.Combinatorics.mem_words
#print axioms contract_JL055
