import JonnyLean.Parsing.Primitives

open JonnyLean.Parsing

theorem contract_JL236 (test : α → Bool) (input rest : List α) (a : α) : satisfy test input = some (a,rest) ↔ input = a::rest ∧ test a = true :=
  satisfy_iff test input rest a

theorem contract_JL236_definition (test : α → Bool) : satisfy test [] = none := rfl

theorem contract_JL236_boundary : satisfy id [false,true] = none := rfl

#print axioms JonnyLean.Parsing.satisfy_iff
#print axioms contract_JL236
