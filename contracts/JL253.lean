import JonnyLean.Encoding.Combinators

open JonnyLean.Encoding
open JonnyLean.Parsing

theorem contract_JL253 (c : Codec α β) (d : Codec α γ) (value : β × γ) (rest : List α) : decodePair c d (encodePair c d value ++ rest) = some (value,rest) :=
  pair_roundtrip c d value rest

theorem contract_JL253_definition (c : Codec α β) (d : Codec α γ) (b : β) (g : γ) : encodePair c d (b,g) = c.encode b ++ d.encode g := rfl

theorem contract_JL253_boundary : decodePair unaryCodec unaryCodec (unary 2 ++ unary 0 ++ [true]) = some ((2,0),[true]) := rfl

#print axioms JonnyLean.Encoding.pair_roundtrip
#print axioms contract_JL253
