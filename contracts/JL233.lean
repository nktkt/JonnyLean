import JonnyLean.Parsing.Core

open JonnyLean.Parsing

theorem contract_JL233 {p : Parser α β} {f : β → Parser α γ} (hp : Safe p) (hf : ∀ b, Safe (f b)) : ∀ input c rest, bindP p f input = some (c,rest) → ∃ consumed, input = consumed ++ rest :=
  bind_safe hp hf

theorem contract_JL233_definition (b : β) (input : List α) : pureP b input = some (b,input) := rfl

theorem contract_JL233_boundary : bindP (failP : Parser Bool Nat) (fun n => pureP (n+1)) [] = none := rfl

#print axioms JonnyLean.Parsing.bind_safe
#print axioms contract_JL233
