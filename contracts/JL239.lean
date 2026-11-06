import JonnyLean.Parsing.Core

open JonnyLean.Parsing

theorem contract_JL239 (f : β → γ) (g : γ → δ) (p : Parser α β) : mapP g (mapP f p) = mapP (fun b => g (f b)) p :=
  map_comp f g p

theorem contract_JL239_definition (f : β → γ) (p : Parser α β) : mapP f p = bindP p (fun b => pureP (f b)) := rfl

theorem contract_JL239_boundary : mapP (fun n => n*2) (pureP 3 : Parser Bool Nat) [true] = some (6,[true]) := rfl

#print axioms JonnyLean.Parsing.map_comp
#print axioms contract_JL239
