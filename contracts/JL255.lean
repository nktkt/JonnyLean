import JonnyLean.Encoding.Combinators

open JonnyLean.Encoding
open JonnyLean.Parsing

theorem contract_JL255 (c : Codec α β) (f : β → γ) (g : γ → β) (fg : ∀ value, f (g value) = value) (value : γ) (rest : List α) : transportDecode c f (transportEncode c g value ++ rest) = some (value,rest) :=
  transport_roundtrip c f g fg value rest

theorem contract_JL255_definition (c : Codec α β) (g : γ → β) (value : γ) : transportEncode c g value = c.encode (g value) := rfl

theorem contract_JL255_boundary : transportDecode unaryCodec id (transportEncode unaryCodec id 2 ++ [false]) = some (2,[false]) := rfl

#print axioms JonnyLean.Encoding.transport_roundtrip
#print axioms contract_JL255
