import JonnyLean.Parsing.Core

open JonnyLean.Parsing

theorem contract_JL235 (p q r : Parser α β) : choice (choice p q) r = choice p (choice q r) :=
  choice_assoc p q r

theorem contract_JL235_definition (q : Parser α β) : choice failP q = q := rfl

theorem contract_JL235_boundary : choice (pureP 1 : Parser Bool Nat) (pureP 2) [] = some (1,[]) := rfl

#print axioms JonnyLean.Parsing.choice_assoc
#print axioms contract_JL235
