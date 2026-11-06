import JonnyLean.Parsing.Primitives

open JonnyLean.Parsing

theorem contract_JL247 (p : Parser α β) (input : List α) (b : β) : complete p input = some b ↔ p input = some (b,[]) :=
  complete_iff p input b

theorem contract_JL247_definition (p : Parser α β) (input : List α) (h : p input = none) : complete p input = none := by simp [complete,h]

theorem contract_JL247_boundary : complete (literal [true]) [true,false] = none := rfl

#print axioms JonnyLean.Parsing.complete_iff
#print axioms contract_JL247
