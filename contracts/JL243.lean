import JonnyLean.Parsing.Repetition

open JonnyLean.Parsing

theorem contract_JL243 {p : Parser α β} (hp : Safe p) (n : Nat) (input : List α) : ∃ consumed, input = consumed ++ (many p n input).2 :=
  many_safe hp n input

theorem contract_JL243_definition (p : Parser α β) (input : List α) : many p 0 input = ([],input) := rfl

theorem contract_JL243_boundary : many (satisfy id) 10 [true,true,false] = ([true,true],[false]) := rfl

#print axioms JonnyLean.Parsing.many_safe
#print axioms contract_JL243
