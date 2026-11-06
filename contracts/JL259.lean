import JonnyLean.Encoding.Trees

open JonnyLean.Encoding
open JonnyLean.Parsing

theorem contract_JL259 (t : Shape) (fuel : Nat) (rest : List Bool) (h : height t < fuel) : decodeTree fuel (encodeTree t ++ rest) = some (t,rest) :=
  tree_roundtrip t fuel rest h

theorem contract_JL259_definition (l r : Shape) : encodeTree (.branch l r) = true :: (encodeTree l ++ encodeTree r) := rfl

theorem contract_JL259_boundary : decodeTree 2 [true,false,false,true] = some (Shape.branch .leaf .leaf,[true]) := rfl

#print axioms JonnyLean.Encoding.tree_roundtrip
#print axioms contract_JL259
