import JonnyLean.Encoding.Blocks

namespace JonnyLean.Encoding
open JonnyLean.Parsing

def unary (n : Nat) : List Bool := List.replicate n true ++ [false]

def readUnary : Parser Bool Nat
  | [] => none
  | false::rest => some (0,rest)
  | true::input => match readUnary input with
      | none => none
      | some (n,rest) => some (n+1,rest)

theorem readUnary_roundtrip (n : Nat) (rest : List Bool) :
    readUnary (unary n ++ rest) = some (n,rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [unary,List.replicate_succ,List.cons_append,readUnary]
    change (match readUnary (unary n ++ rest) with
      | none => none
      | some (m,tail) => some (m+1,tail)) = some (n+1,rest)
    rw [ih]

theorem readUnary_sound (input : List Bool) (n : Nat) (rest : List Bool)
    (h : readUnary input = some (n,rest)) : input = unary n ++ rest := by
  induction input generalizing n with
  | nil => cases h
  | cons token input ih =>
    cases token with
    | false => cases h; rfl
    | true =>
      cases e : readUnary input with
      | none => simp [readUnary,e] at h
      | some result =>
        rcases result with ⟨m,tail⟩
        simp [readUnary,e] at h
        rcases h with ⟨rfl,rfl⟩
        simpa [unary,List.replicate_succ] using congrArg (List.cons true) (ih m e)

theorem readUnary_exact (input : List Bool) (n : Nat) (rest : List Bool) :
    readUnary input = some (n,rest) ↔ input = unary n ++ rest :=
  ⟨readUnary_sound input n rest,fun h => h ▸ readUnary_roundtrip n rest⟩

theorem unary_length (n : Nat) : (unary n).length = n+1 := by simp [unary]

theorem readUnary_consumption {input rest : List Bool} {n : Nat}
    (h : readUnary input = some (n,rest)) :
    input.length = n + 1 + rest.length ∧ rest.length < input.length := by
  rw [(readUnary_exact _ _ _).mp h,List.length_append,unary_length]
  constructor
  · rfl
  · omega

theorem unary_prefix_free (m n : Nat) (u v : List Bool)
    (h : unary m ++ u = unary n ++ v) : m = n ∧ u = v := by
  have e := congrArg readUnary h
  simpa [readUnary_roundtrip] using e

theorem readUnary_unterminated (n : Nat) : readUnary (List.replicate n true) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,readUnary,ih]

end JonnyLean.Encoding
