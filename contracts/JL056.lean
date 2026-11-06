import JonnyLean.Combinatorics.WordCount

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.Combinatorics

theorem contract_JL056 {α : Type u} (alphabet : List α) (n : Nat) :
    (words alphabet n).length = alphabet.length ^ n := length_words alphabet n

example : (words ([] : List Bool) 0).length = 1 := rfl
example (n : Nat) : words ([] : List Bool) (n + 1) = [] := words_empty_succ n
example : (words [false, true] 3).length = 8 := rfl
example : (words [true, true] 2).length = 4 := rfl
example (a : α) (n : Nat) : (words [a] n).length = 1 := length_words_singleton a n

#print axioms JonnyLean.Combinatorics.length_words
#print axioms contract_JL056
