import JonnyLean.Encoding.Blocks

open JonnyLean.Encoding
open JonnyLean.Parsing

theorem contract_JL249 (input : List (Option α)) (xs : List α) (rest : List (Option α)) : decodeBlock input = some (xs,rest) ↔ input = encodeBlock xs ++ rest :=
  decodeBlock_exact input xs rest

theorem contract_JL249_definition (xs : List α) : encodeBlock xs = xs.map some ++ [none] := rfl

theorem contract_JL249_boundary : decodeBlock [some 1,some 2] = (none : Option (List Nat × List (Option Nat))) := rfl

#print axioms JonnyLean.Encoding.decodeBlock_exact
#print axioms contract_JL249
