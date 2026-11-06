import JonnyLean.Parsing.Primitives

open JonnyLean.Parsing

theorem contract_JL248 (test : β → Bool) (p : Parser α β) (input rest : List α) (b : β) : guardP test p input = some (b,rest) ↔ p input = some (b,rest) ∧ test b = true :=
  guard_iff test p input rest b

theorem contract_JL248_definition (test : β → Bool) (p : Parser α β) : guardP test p = bindP p (fun b => if test b then pureP b else failP) := rfl

theorem contract_JL248_boundary : guardP (fun n => n > 3) (pureP 2 : Parser Bool Nat) [] = none := rfl

#print axioms JonnyLean.Parsing.guard_iff
#print axioms contract_JL248
