import JonnyLean.Parsing.Core

namespace JonnyLean.Parsing

def satisfy (test : α → Bool) : Parser α α
  | [] => none
  | a::rest => if test a then some (a,rest) else none

theorem satisfy_iff (test : α → Bool) (input rest : List α) (a : α) :
    satisfy test input = some (a,rest) ↔ input = a::rest ∧ test a = true := by
  cases input with
  | nil => simp [satisfy]
  | cons b tail =>
    by_cases h : test b = true
    · simp [satisfy,h,Prod.ext_iff,and_assoc]
      intro hab _
      simpa [← hab] using h
    · simp [satisfy,h]
      intro e _
      cases e
      exact Bool.eq_false_iff.mpr h

theorem satisfy_safe (test : α → Bool) : Safe (satisfy test) := by
  intro input a rest h
  exact ⟨[a],(satisfy_iff _ _ _ _).mp h |>.1⟩

def literal [DecidableEq α] : List α → Parser α Unit
  | [] => pureP ()
  | a::word => fun input => match input with
      | [] => none
      | b::rest => if b = a then literal word rest else none

theorem literal_iff [DecidableEq α] (word input rest : List α) :
    literal word input = some ((),rest) ↔ input = word ++ rest := by
  induction word generalizing input with
  | nil => simp [literal,pureP]
  | cons a word ih =>
    cases input with
    | nil => simp [literal]
    | cons b tail =>
      by_cases h : b = a
      · subst b; simp [literal,ih]
      · simp [literal,h]

theorem literal_safe [DecidableEq α] (word : List α) : Safe (literal word) := by
  intro input b rest h
  cases b
  exact ⟨word,(literal_iff _ _ _).mp h⟩

theorem literal_append [DecidableEq α] (u v : List α) :
    bindP (literal u) (fun _ => literal v) = literal (u ++ v) := by
  funext input
  induction u generalizing input with
  | nil => rfl
  | cons a u ih =>
    cases input with
    | nil => rfl
    | cons b tail =>
      by_cases h : b = a
      · simpa [literal,h,bindP] using ih tail
      · simp [literal,h,bindP]

def lookAhead (p : Parser α β) : Parser α β := fun input =>
  match p input with
  | none => none
  | some (b,_) => some (b,input)

theorem lookAhead_iff (p : Parser α β) (input rest : List α) (b : β) :
    lookAhead p input = some (b,rest) ↔
      rest = input ∧ ∃ discarded, p input = some (b,discarded) := by
  cases h : p input with
  | none => simp [lookAhead,h]
  | some result =>
    rcases result with ⟨c,tail⟩
    simp [lookAhead,h,Prod.ext_iff,and_comm,eq_comm]

theorem lookAhead_safe (p : Parser α β) : Safe (lookAhead p) := by
  intro input b rest h
  exact ⟨[],by simpa using ((lookAhead_iff _ _ _ _).mp h).1.symm⟩

def eof : Parser α Unit
  | [] => some ((),[])
  | _::_ => none

theorem eof_iff (input rest : List α) :
    eof input = some ((),rest) ↔ input = [] ∧ rest = [] := by
  cases input <;> simp [eof,eq_comm]

def complete (p : Parser α β) (input : List α) : Option β :=
  match p input with
  | some (b,[]) => some b
  | _ => none

theorem complete_iff (p : Parser α β) (input : List α) (b : β) :
    complete p input = some b ↔ p input = some (b,[]) := by
  cases h : p input with
  | none => simp [complete,h]
  | some result =>
    rcases result with ⟨c,rest⟩
    cases rest <;> simp [complete,h]

def guardP (test : β → Bool) (p : Parser α β) : Parser α β :=
  bindP p (fun b => if test b then pureP b else failP)

theorem guard_iff (test : β → Bool) (p : Parser α β) (input rest : List α) (b : β) :
    guardP test p input = some (b,rest) ↔ p input = some (b,rest) ∧ test b = true := by
  cases h : p input with
  | none => simp [guardP,bindP,h]
  | some result =>
    rcases result with ⟨c,tail⟩
    by_cases k : test c = true
    · simp [guardP,bindP,pureP,h,k,Prod.ext_iff,and_assoc]
      intro hcb _
      simpa [← hcb] using k
    · simp [guardP,bindP,failP,h,k]
      intro e _
      cases e
      exact Bool.eq_false_iff.mpr k

end JonnyLean.Parsing
