import JonnyLean.Parsing.Primitives

open JonnyLean.Parsing

theorem contract_JL238 [DecidableEq α] (u v : List α) : bindP (literal u) (fun _ => literal v) = literal (u ++ v) :=
  literal_append u v

theorem contract_JL238_definition [DecidableEq α] (a : α) : literal [a] [] = none := rfl

theorem contract_JL238_boundary : bindP (literal [true]) (fun _ => literal [false]) [true,true] = none := by decide

#print axioms JonnyLean.Parsing.literal_append
#print axioms contract_JL238
