import JonnyLean.Encoding.Unary

namespace JonnyLean.Encoding
open JonnyLean.Parsing

structure Codec (α : Type u) (β : Type v) where
  encode : β → List α
  decode : Parser α β
  roundtrip : ∀ b rest, decode (encode b ++ rest) = some (b,rest)
  sound : ∀ input b rest, decode input = some (b,rest) → input = encode b ++ rest

theorem codec_exact (c : Codec α β) (input rest : List α) (b : β) :
    c.decode input = some (b,rest) ↔ input = c.encode b ++ rest :=
  ⟨c.sound input b rest,fun h => h ▸ c.roundtrip b rest⟩

theorem codec_prefix_free (c : Codec α β) (b d : β) (u v : List α)
    (h : c.encode b ++ u = c.encode d ++ v) : b = d ∧ u = v := by
  have e := congrArg c.decode h
  simpa [c.roundtrip] using e

def blockCodec : Codec (Option α) (List α) :=
  ⟨encodeBlock,decodeBlock,decodeBlock_roundtrip,decodeBlock_sound⟩
def unaryCodec : Codec Bool Nat := ⟨unary,readUnary,readUnary_roundtrip,readUnary_sound⟩

def encodePair (c : Codec α β) (d : Codec α γ) (value : β × γ) : List α :=
  c.encode value.1 ++ d.encode value.2

def decodePair (c : Codec α β) (d : Codec α γ) : Parser α (β × γ) := pairP c.decode d.decode

theorem pair_roundtrip (c : Codec α β) (d : Codec α γ) (value : β × γ) (rest : List α) :
    decodePair c d (encodePair c d value ++ rest) = some (value,rest) := by
  rcases value with ⟨b,g⟩
  simp [decodePair,encodePair,pairP,bindP,mapP,pureP,List.append_assoc,c.roundtrip,d.roundtrip]

theorem pair_sound (c : Codec α β) (d : Codec α γ) (input rest : List α) (value : β × γ)
    (h : decodePair c d input = some (value,rest)) : input = encodePair c d value ++ rest := by
  rcases value with ⟨b,g⟩
  obtain ⟨middle,hc,hd⟩ := (pair_iff c.decode d.decode input rest b g).mp h
  have e := c.sound input b middle hc
  have f := d.sound middle g rest hd
  simpa [encodePair,f,List.append_assoc] using e

def pairCodec (c : Codec α β) (d : Codec α γ) : Codec α (β × γ) :=
  ⟨encodePair c d,decodePair c d,pair_roundtrip c d,fun i b r h => pair_sound c d i r b h⟩

def encodeSum (c : Codec Bool β) (d : Codec Bool γ) : Sum β γ → List Bool
  | .inl b => false::c.encode b
  | .inr g => true::d.encode g

def decodeSum (c : Codec Bool β) (d : Codec Bool γ) : Parser Bool (Sum β γ)
  | [] => none
  | false::input => mapP Sum.inl c.decode input
  | true::input => mapP Sum.inr d.decode input

theorem sum_roundtrip (c : Codec Bool β) (d : Codec Bool γ) (value : Sum β γ) (rest : List Bool) :
    decodeSum c d (encodeSum c d value ++ rest) = some (value,rest) := by
  cases value <;> simp [encodeSum,decodeSum,mapP,bindP,pureP,c.roundtrip,d.roundtrip]

theorem sum_sound (c : Codec Bool β) (d : Codec Bool γ) (input rest : List Bool) (value : Sum β γ)
    (h : decodeSum c d input = some (value,rest)) : input = encodeSum c d value ++ rest := by
  cases input with
  | nil => cases h
  | cons tag input =>
    cases tag with
    | false =>
      cases e : c.decode input with
      | none => simp [decodeSum,mapP,bindP,e] at h
      | some result =>
        rcases result with ⟨b,tail⟩
        simp [decodeSum,mapP,bindP,pureP,e] at h
        rcases h with ⟨rfl,rfl⟩
        simpa [encodeSum] using congrArg (List.cons false) (c.sound input b _ e)
    | true =>
      cases e : d.decode input with
      | none => simp [decodeSum,mapP,bindP,e] at h
      | some result =>
        rcases result with ⟨g,tail⟩
        simp [decodeSum,mapP,bindP,pureP,e] at h
        rcases h with ⟨rfl,rfl⟩
        simpa [encodeSum] using congrArg (List.cons true) (d.sound input g _ e)

def sumCodec (c : Codec Bool β) (d : Codec Bool γ) : Codec Bool (Sum β γ) :=
  ⟨encodeSum c d,decodeSum c d,sum_roundtrip c d,fun i b r h => sum_sound c d i r b h⟩

def transportEncode (c : Codec α β) (g : γ → β) (value : γ) : List α := c.encode (g value)
def transportDecode (c : Codec α β) (f : β → γ) : Parser α γ := mapP f c.decode

theorem transport_roundtrip (c : Codec α β) (f : β → γ) (g : γ → β)
    (fg : ∀ value, f (g value) = value) (value : γ) (rest : List α) :
    transportDecode c f (transportEncode c g value ++ rest) = some (value,rest) := by
  simp [transportDecode,transportEncode,mapP,bindP,pureP,c.roundtrip,fg]

theorem transport_sound (c : Codec α β) (f : β → γ) (g : γ → β)
    (gf : ∀ value, g (f value) = value) (input rest : List α) (value : γ)
    (h : transportDecode c f input = some (value,rest)) : input = transportEncode c g value ++ rest := by
  cases e : c.decode input with
  | none => simp [transportDecode,mapP,bindP,e] at h
  | some result =>
    rcases result with ⟨b,tail⟩
    simp [transportDecode,mapP,bindP,pureP,e] at h
    rcases h with ⟨rfl,rfl⟩
    simpa [transportEncode,gf] using c.sound input b _ e

def transportCodec (c : Codec α β) (f : β → γ) (g : γ → β)
    (fg : ∀ value, f (g value) = value) (gf : ∀ value, g (f value) = value) : Codec α γ :=
  ⟨transportEncode c g,transportDecode c f,transport_roundtrip c f g fg,
    fun i b r h => transport_sound c f g gf i r b h⟩

end JonnyLean.Encoding
