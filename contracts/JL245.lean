import JonnyLean.Parsing.Primitives

open JonnyLean.Parsing

theorem contract_JL245 (p : Parser α β) (input rest : List α) (b : β) : lookAhead p input = some (b,rest) ↔ rest = input ∧ ∃ discarded, p input = some (b,discarded) :=
  lookAhead_iff p input rest b

theorem contract_JL245_definition (p : Parser α β) (input : List α) (h : p input = none) : lookAhead p input = none := by simp [lookAhead,h]

theorem contract_JL245_boundary : lookAhead (satisfy id) [true,false] = some (true,[true,false]) := rfl

#print axioms JonnyLean.Parsing.lookAhead_iff
#print axioms contract_JL245
