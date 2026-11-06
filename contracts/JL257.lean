import JonnyLean.Encoding.FramedLists

open JonnyLean.Encoding
open JonnyLean.Parsing

theorem contract_JL257 (c : Codec Bool β) (xs : List β) (rest : List Bool) : decodeList c (encodeList c xs ++ rest) = some (xs,rest) :=
  list_roundtrip c xs rest

theorem contract_JL257_definition (c : Codec Bool β) (xs : List β) : encodeList c xs = unary xs.length ++ encodeFields c xs := rfl

theorem contract_JL257_boundary : decodeList unaryCodec (encodeList unaryCodec [0,2] ++ [true]) = some ([0,2],[true]) := rfl

#print axioms JonnyLean.Encoding.list_roundtrip
#print axioms contract_JL257
