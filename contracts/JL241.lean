import JonnyLean.Parsing.Repetition

open JonnyLean.Parsing

theorem contract_JL241 (p : Parser α β) (n : Nat) (input rest : List α) (bs : List β) : repeatP p n input = some (bs,rest) ↔ Chain p n input bs rest :=
  repeat_iff p n input rest bs

theorem contract_JL241_definition (p : Parser α β) (input : List α) : repeatP p 0 input = some ([],input) := rfl

theorem contract_JL241_boundary : repeatP (satisfy id) 2 [true,true,false] = some ([true,true],[false]) := rfl

#print axioms JonnyLean.Parsing.repeat_iff
#print axioms contract_JL241
