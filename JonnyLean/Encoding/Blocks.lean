import JonnyLean.Parsing.Repetition

namespace JonnyLean.Encoding
open JonnyLean.Parsing

def encodeBlock (xs : List α) : List (Option α) := xs.map some ++ [none]

def decodeBlock : Parser (Option α) (List α)
  | [] => none
  | none::rest => some ([],rest)
  | some a::input =>
    match decodeBlock input with
    | none => none
    | some (xs,rest) => some (a::xs,rest)

theorem decodeBlock_roundtrip (xs : List α) (rest : List (Option α)) :
    decodeBlock (encodeBlock xs ++ rest) = some (xs,rest) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (match decodeBlock (encodeBlock xs ++ rest) with
      | none => none
      | some (ys,tail) => some (a::ys,tail)) = some (a::xs,rest)
    rw [ih]

theorem decodeBlock_sound (input : List (Option α)) (xs : List α) (rest : List (Option α))
    (h : decodeBlock input = some (xs,rest)) : input = encodeBlock xs ++ rest := by
  induction input generalizing xs with
  | nil => cases h
  | cons token input ih =>
    cases token with
    | none => cases h; rfl
    | some a =>
      cases e : decodeBlock input with
      | none => simp [decodeBlock,e] at h
      | some result =>
        rcases result with ⟨ys,tail⟩
        simp [decodeBlock,e] at h
        rcases h with ⟨rfl,rfl⟩
        simpa [encodeBlock] using congrArg (List.cons (some a)) (ih ys e)

theorem decodeBlock_exact (input : List (Option α)) (xs : List α) (rest : List (Option α)) :
    decodeBlock input = some (xs,rest) ↔ input = encodeBlock xs ++ rest :=
  ⟨decodeBlock_sound input xs rest,fun h => h ▸ decodeBlock_roundtrip xs rest⟩

theorem block_prefix_free (xs ys : List α) (u v : List (Option α))
    (h : encodeBlock xs ++ u = encodeBlock ys ++ v) : xs = ys ∧ u = v := by
  have e := congrArg decodeBlock h
  simpa [decodeBlock_roundtrip] using e

theorem block_length (xs : List α) : (encodeBlock xs).length = xs.length + 1 := by
  simp [encodeBlock]

theorem decodeBlock_unterminated (xs : List α) : decodeBlock (xs.map some) = none := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [decodeBlock,ih]

end JonnyLean.Encoding
