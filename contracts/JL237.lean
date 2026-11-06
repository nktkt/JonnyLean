import JonnyLean.Parsing.Primitives

open JonnyLean.Parsing

theorem contract_JL237 [DecidableEq α] (word input rest : List α) : literal word input = some ((),rest) ↔ input = word ++ rest :=
  literal_iff word input rest

theorem contract_JL237_definition [DecidableEq α] (input : List α) : literal [] input = some ((),input) := rfl

theorem contract_JL237_boundary : literal [true,false] [true,false,true] = some ((),[true]) := by decide

#print axioms JonnyLean.Parsing.literal_iff
#print axioms contract_JL237
