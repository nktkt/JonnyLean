import JonnyLean.Parsing.Repetition

open JonnyLean.Parsing

theorem contract_JL242 {p : Parser α β} {n : Nat} {input rest : List α} {bs : List β} (h : repeatP p n input = some (bs,rest)) : bs.length = n :=
  repeat_length h

theorem contract_JL242_definition (p : Parser α β) (n : Nat) : repeatP p (n+1) = bindP p (fun b => mapP (List.cons b) (repeatP p n)) := rfl

theorem contract_JL242_boundary : repeatP (pureP 7 : Parser Bool Nat) 3 [] = some ([7,7,7],[]) := rfl

#print axioms JonnyLean.Parsing.repeat_length
#print axioms contract_JL242
