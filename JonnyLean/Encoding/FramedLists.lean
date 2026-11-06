import JonnyLean.Encoding.Combinators

namespace JonnyLean.Encoding
open JonnyLean.Parsing

def encodeFields (c : Codec α β) (xs : List β) : List α := xs.flatMap c.encode

def decodeFields (c : Codec α β) (n : Nat) : Parser α (List β) := repeatP c.decode n

theorem fields_roundtrip (c : Codec α β) (xs : List β) (rest : List α) :
    decodeFields c xs.length (encodeFields c xs ++ rest) = some (xs,rest) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [decodeFields,encodeFields] at ih
    simp [decodeFields,encodeFields,repeatP,bindP,mapP,pureP,List.append_assoc,c.roundtrip,ih]

theorem chain_fields_sound (c : Codec α β) {n : Nat} {input rest : List α} {xs : List β}
    (h : Chain c.decode n input xs rest) : input = encodeFields c xs ++ rest := by
  induction h with
  | nil input => rfl
  | @step n input middle rest b bs hp hc ih =>
    have hs := c.sound input b middle hp
    simpa [encodeFields,ih,List.append_assoc] using hs

theorem fields_sound (c : Codec α β) (n : Nat) (input rest : List α) (xs : List β)
    (h : decodeFields c n input = some (xs,rest)) :
    input = encodeFields c xs ++ rest ∧ xs.length = n := by
  have hc := (repeat_iff c.decode n input rest xs).mp h
  exact ⟨chain_fields_sound c hc,chain_length hc⟩

def encodeList (c : Codec Bool β) (xs : List β) : List Bool :=
  unary xs.length ++ encodeFields c xs

def decodeList (c : Codec Bool β) : Parser Bool (List β) :=
  bindP readUnary (fun n => decodeFields c n)

theorem list_roundtrip (c : Codec Bool β) (xs : List β) (rest : List Bool) :
    decodeList c (encodeList c xs ++ rest) = some (xs,rest) := by
  simp [decodeList,encodeList,bindP,List.append_assoc,readUnary_roundtrip,fields_roundtrip]

theorem list_sound (c : Codec Bool β) (input rest : List Bool) (xs : List β)
    (h : decodeList c input = some (xs,rest)) : input = encodeList c xs ++ rest := by
  cases e : readUnary input with
  | none => simp [decodeList,bindP,e] at h
  | some result =>
    rcases result with ⟨n,middle⟩
    have hf : decodeFields c n middle = some (xs,rest) := by simpa [decodeList,bindP,e] using h
    obtain ⟨hm,hn⟩ := fields_sound c n middle rest xs hf
    have hi := readUnary_sound input n middle e
    simpa [encodeList,hn,hm,List.append_assoc] using hi

theorem list_exact (c : Codec Bool β) (input rest : List Bool) (xs : List β) :
    decodeList c input = some (xs,rest) ↔ input = encodeList c xs ++ rest :=
  ⟨list_sound c input rest xs,fun h => h ▸ list_roundtrip c xs rest⟩

def listCodec (c : Codec Bool β) : Codec Bool (List β) :=
  ⟨encodeList c,decodeList c,list_roundtrip c,fun i b r h => list_sound c i r b h⟩

theorem list_prefix_free (c : Codec Bool β) (xs ys : List β) (u v : List Bool)
    (h : encodeList c xs ++ u = encodeList c ys ++ v) : xs = ys ∧ u = v :=
  codec_prefix_free (listCodec c) xs ys u v h

theorem decodeList_empty_input (c : Codec Bool β) : decodeList c [] = none := rfl

end JonnyLean.Encoding
