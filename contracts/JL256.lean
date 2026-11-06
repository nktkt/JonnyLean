import JonnyLean.Encoding.FramedLists

open JonnyLean.Encoding
open JonnyLean.Parsing

theorem contract_JL256 (c : Codec α β) (xs : List β) (rest : List α) : decodeFields c xs.length (encodeFields c xs ++ rest) = some (xs,rest) :=
  fields_roundtrip c xs rest

theorem contract_JL256_definition (c : Codec α β) (xs : List β) : encodeFields c xs = xs.flatMap c.encode := rfl

theorem contract_JL256_boundary : decodeFields unaryCodec 2 (unary 1 ++ unary 2 ++ [true]) = some ([1,2],[true]) := rfl

#print axioms JonnyLean.Encoding.fields_roundtrip
#print axioms contract_JL256
