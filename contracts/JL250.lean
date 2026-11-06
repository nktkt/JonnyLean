import JonnyLean.Encoding.Blocks

open JonnyLean.Encoding
open JonnyLean.Parsing

theorem contract_JL250 (xs ys : List α) (u v : List (Option α)) (h : encodeBlock xs ++ u = encodeBlock ys ++ v) : xs = ys ∧ u = v :=
  block_prefix_free xs ys u v h

theorem contract_JL250_definition : encodeBlock ([] : List Nat) = [none] := rfl

theorem contract_JL250_boundary : decodeBlock [none,some 7] = some (([] : List Nat),[some 7]) := rfl

#print axioms JonnyLean.Encoding.block_prefix_free
#print axioms contract_JL250
