import JonnyLean.Encoding.FramedLists

namespace JonnyLean.Encoding
open JonnyLean.Parsing

inductive Shape where
  | leaf : Shape
  | branch : Shape → Shape → Shape
  deriving DecidableEq

def height : Shape → Nat
  | .leaf => 0
  | .branch l r => max (height l) (height r) + 1

def branches : Shape → Nat
  | .leaf => 0
  | .branch l r => branches l + branches r + 1

def encodeTree : Shape → List Bool
  | .leaf => [false]
  | .branch l r => true :: (encodeTree l ++ encodeTree r)

def decodeTree : Nat → Parser Bool Shape
  | 0 => failP
  | fuel+1 => fun input => match input with
      | [] => none
      | false::rest => some (.leaf,rest)
      | true::input =>
        match decodeTree fuel input with
        | none => none
        | some (l,middle) => match decodeTree fuel middle with
            | none => none
            | some (r,rest) => some (.branch l r,rest)

theorem tree_roundtrip (t : Shape) (fuel : Nat) (rest : List Bool) (h : height t < fuel) :
    decodeTree fuel (encodeTree t ++ rest) = some (t,rest) := by
  induction t generalizing fuel rest with
  | leaf => cases fuel with
    | zero => simp [height] at h
    | succ fuel => rfl
  | branch l r il ir =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hl : height l < fuel := by simp only [height] at h; omega
      have hr : height r < fuel := by simp only [height] at h; omega
      simp only [encodeTree,List.cons_append,List.append_assoc,decodeTree]
      rw [il fuel (encodeTree r ++ rest) hl]
      simp only [ir fuel rest hr]

theorem tree_sound (fuel : Nat) (input rest : List Bool) (t : Shape)
    (h : decodeTree fuel input = some (t,rest)) :
    input = encodeTree t ++ rest ∧ height t < fuel := by
  induction fuel generalizing input rest t with
  | zero => cases h
  | succ fuel ih =>
    cases input with
    | nil => cases h
    | cons token input =>
      cases token with
      | false => cases h; exact ⟨rfl,by simp [height]⟩
      | true =>
        cases e : decodeTree fuel input with
        | none => simp [decodeTree,e] at h
        | some result =>
          rcases result with ⟨l,middle⟩
          cases f : decodeTree fuel middle with
          | none => simp [decodeTree,e,f] at h
          | some result =>
            rcases result with ⟨r,tail⟩
            simp [decodeTree,e,f] at h
            rcases h with ⟨rfl,rfl⟩
            obtain ⟨he,hl⟩ := ih input middle l e
            obtain ⟨hf,hr⟩ := ih middle tail r f
            constructor
            · simp [encodeTree,he,hf,List.append_assoc]
            · simp only [height]; omega

theorem tree_exact (fuel : Nat) (input rest : List Bool) (t : Shape) :
    decodeTree fuel input = some (t,rest) ↔ input = encodeTree t ++ rest ∧ height t < fuel := by
  constructor
  · exact tree_sound fuel input rest t
  · rintro ⟨rfl,h⟩; exact tree_roundtrip t fuel rest h

theorem tree_prefix_free (s t : Shape) (u v : List Bool)
    (h : encodeTree s ++ u = encodeTree t ++ v) : s = t ∧ u = v := by
  let fuel := max (height s) (height t) + 1
  have hs : height s < fuel := by dsimp [fuel]; omega
  have ht : height t < fuel := by dsimp [fuel]; omega
  have e := congrArg (decodeTree fuel) h
  rw [tree_roundtrip s fuel u hs,tree_roundtrip t fuel v ht] at e
  simpa using e

theorem tree_encoding_injective {s t : Shape} (h : encodeTree s = encodeTree t) : s = t :=
  (tree_prefix_free s t [] [] (by simpa using h)).1

theorem tree_code_length (t : Shape) : (encodeTree t).length = 2 * branches t + 1 := by
  induction t with
  | leaf => rfl
  | branch l r il ir => simp [encodeTree,branches,il,ir]; omega

theorem decodeTree_empty (fuel : Nat) : decodeTree fuel [] = none := by cases fuel <;> rfl

end JonnyLean.Encoding
