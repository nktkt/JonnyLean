import JonnyLean.Encoding.Unary

open JonnyLean.Encoding
open JonnyLean.Parsing

theorem contract_JL252 {input rest : List Bool} {n : Nat} (h : readUnary input = some (n,rest)) : input.length = n + 1 + rest.length ∧ rest.length < input.length :=
  readUnary_consumption h

theorem contract_JL252_definition : unary 0 = [false] := rfl

theorem contract_JL252_boundary : readUnary [false,true] = some (0,[true]) := rfl

#print axioms JonnyLean.Encoding.readUnary_consumption
#print axioms contract_JL252
