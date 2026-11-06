import JonnyLean.Encoding.FramedLists

open JonnyLean.Encoding
open JonnyLean.Parsing

theorem contract_JL258 (c : Codec Bool β) (input rest : List Bool) (xs : List β) : decodeList c input = some (xs,rest) ↔ input = encodeList c xs ++ rest :=
  list_exact c input rest xs

theorem contract_JL258_definition (c : Codec Bool β) : decodeList c [] = none := rfl

theorem contract_JL258_boundary : decodeList unaryCodec [true,false] = none := rfl

#print axioms JonnyLean.Encoding.list_exact
#print axioms contract_JL258
