import JonnyLean.Parsing.Primitives

open JonnyLean.Parsing

theorem contract_JL246 (input rest : List α) : eof input = some ((),rest) ↔ input = [] ∧ rest = [] :=
  eof_iff input rest

theorem contract_JL246_definition : (eof : Parser Bool Unit) [] = some ((),[]) := rfl

theorem contract_JL246_boundary : (eof : Parser Bool Unit) [true] = none := rfl

#print axioms JonnyLean.Parsing.eof_iff
#print axioms contract_JL246
