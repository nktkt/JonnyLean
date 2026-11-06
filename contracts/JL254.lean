import JonnyLean.Encoding.Combinators

open JonnyLean.Encoding
open JonnyLean.Parsing

theorem contract_JL254 (c : Codec Bool β) (d : Codec Bool γ) (value : Sum β γ) (rest : List Bool) : decodeSum c d (encodeSum c d value ++ rest) = some (value,rest) :=
  sum_roundtrip c d value rest

theorem contract_JL254_definition (c : Codec Bool β) (d : Codec Bool γ) (b : β) : encodeSum c d (.inl b) = false::c.encode b := rfl

theorem contract_JL254_boundary : decodeSum unaryCodec unaryCodec [true,false,false] = some (Sum.inr 0,[false]) := rfl

#print axioms JonnyLean.Encoding.sum_roundtrip
#print axioms contract_JL254
