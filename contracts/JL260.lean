import JonnyLean.Encoding.Trees

open JonnyLean.Encoding
open JonnyLean.Parsing

theorem contract_JL260 (s t : Shape) (u v : List Bool) (h : encodeTree s ++ u = encodeTree t ++ v) : s = t ∧ u = v :=
  tree_prefix_free s t u v h

theorem contract_JL260_definition : encodeTree Shape.leaf = [false] := rfl

theorem contract_JL260_boundary : decodeTree 1 [true,false,false] = none := rfl

#print axioms JonnyLean.Encoding.tree_prefix_free
#print axioms contract_JL260
