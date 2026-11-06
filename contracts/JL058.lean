import JonnyLean.Combinatorics.Binomial

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.Combinatorics

theorem contract_JL058 {α : Type u} (xs : List α) (k : Nat) :
    (selections k xs).length = binomial xs.length k := length_selections xs k

example (n : Nat) : binomial n 0 = 1 := binomial_zero n
example (k : Nat) : binomial 0 (k + 1) = 0 := rfl
example (n k : Nat) : binomial (n + 1) (k + 1) = binomial n k + binomial n (k + 1) := rfl
example : binomial 0 0 = 1 := rfl
example : binomial 5 2 = 10 := rfl
example : binomial 3 4 = 0 := rfl
example (n : Nat) : binomial n n = 1 := binomial_diagonal n

#print axioms JonnyLean.Combinatorics.length_selections
#print axioms contract_JL058
