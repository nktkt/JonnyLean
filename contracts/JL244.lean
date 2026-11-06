import JonnyLean.Parsing.Repetition

open JonnyLean.Parsing

theorem contract_JL244 (p : Parser α β) (n : Nat) (input : List α) : (many p n input).1.length ≤ n ∧ ((many p n input).1.length < n → p (many p n input).2 = none) :=
  many_bounds p n input

theorem contract_JL244_definition (p : Parser α β) (n : Nat) (input : List α) (h : p input = none) : many p (n+1) input = ([],input) := by simp [many,h]

theorem contract_JL244_boundary : many (pureP 7 : Parser Bool Nat) 3 [] = ([7,7,7],[]) := rfl

#print axioms JonnyLean.Parsing.many_bounds
#print axioms contract_JL244
