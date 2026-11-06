import JonnyLean.Encoding.Unary

open JonnyLean.Encoding
open JonnyLean.Parsing

theorem contract_JL251 (input : List Bool) (n : Nat) (rest : List Bool) : readUnary input = some (n,rest) ↔ input = unary n ++ rest :=
  readUnary_exact input n rest

theorem contract_JL251_definition (n : Nat) : unary n = List.replicate n true ++ [false] := rfl

theorem contract_JL251_boundary : readUnary [true,true,false,true] = some (2,[true]) := rfl

#print axioms JonnyLean.Encoding.readUnary_exact
#print axioms contract_JL251
