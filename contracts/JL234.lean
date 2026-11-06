import JonnyLean.Parsing.Core

open JonnyLean.Parsing

theorem contract_JL234 (p : Parser α β) (f : β → Parser α γ) (g : γ → Parser α δ) : bindP (bindP p f) g = bindP p (fun b => bindP (f b) g) :=
  bind_assoc p f g

theorem contract_JL234_definition (b : β) (f : β → Parser α γ) : bindP (pureP b) f = f b := rfl

theorem contract_JL234_boundary : bindP (pureP 3 : Parser Bool Nat) (fun n => pureP (n+2)) [] = some (5,[]) := rfl

#print axioms JonnyLean.Parsing.bind_assoc
#print axioms contract_JL234
