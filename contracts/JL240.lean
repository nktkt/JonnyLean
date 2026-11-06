import JonnyLean.Parsing.Core

open JonnyLean.Parsing

theorem contract_JL240 (p : Parser α β) (q : Parser α γ) (input rest : List α) (b : β) (c : γ) : pairP p q input = some ((b,c),rest) ↔ ∃ middle, p input = some (b,middle) ∧ q middle = some (c,rest) :=
  pair_iff p q input rest b c

theorem contract_JL240_definition (p : Parser α β) (q : Parser α γ) : pairP p q = bindP p (fun b => mapP (fun c => (b,c)) q) := rfl

theorem contract_JL240_boundary : pairP (pureP true : Parser Bool Bool) (pureP false) [true] = some ((true,false),[true]) := rfl

#print axioms JonnyLean.Parsing.pair_iff
#print axioms contract_JL240
