import JonnyLean.Parsing.Primitives
import Init.Omega

namespace JonnyLean.Parsing

def repeatP (p : Parser α β) : Nat → Parser α (List β)
  | 0 => pureP []
  | n+1 => bindP p (fun b => mapP (List.cons b) (repeatP p n))

inductive Chain (p : Parser α β) : Nat → List α → List β → List α → Prop where
  | nil (input : List α) : Chain p 0 input [] input
  | step {n : Nat} {input middle rest : List α} {b : β} {bs : List β} :
      p input = some (b,middle) → Chain p n middle bs rest →
      Chain p (n+1) input (b::bs) rest

theorem repeat_iff (p : Parser α β) (n : Nat) (input rest : List α) (bs : List β) :
    repeatP p n input = some (bs,rest) ↔ Chain p n input bs rest := by
  induction n generalizing input bs with
  | zero =>
    constructor
    · intro h; cases h; exact .nil _
    · intro h; cases h; rfl
  | succ n ih =>
    constructor
    · intro h
      cases e : p input with
      | none => simp [repeatP,bindP,e] at h
      | some result =>
        rcases result with ⟨b,middle⟩
        cases k : repeatP p n middle with
        | none => simp [repeatP,bindP,mapP,e,k] at h
        | some result =>
          rcases result with ⟨cs,tail⟩
          simp [repeatP,bindP,mapP,pureP,e,k] at h
          rcases h with ⟨rfl,rfl⟩
          exact .step e ((ih middle cs).mp k)
    · intro h
      cases h with
      | step hp hc =>
        simp [repeatP,bindP,mapP,pureP,hp,(ih _ _).mpr hc]

theorem chain_length {p : Parser α β} {n : Nat} {input rest : List α} {bs : List β}
    (h : Chain p n input bs rest) : bs.length = n := by
  induction h with
  | nil => rfl
  | step hp hc ih => simp [ih]

theorem repeat_length {p : Parser α β} {n : Nat} {input rest : List α} {bs : List β}
    (h : repeatP p n input = some (bs,rest)) : bs.length = n :=
  chain_length ((repeat_iff _ _ _ _ _).mp h)

theorem repeat_safe {p : Parser α β} (hp : Safe p) (n : Nat) : Safe (repeatP p n) := by
  induction n with
  | zero => exact pure_safe []
  | succ n ih => exact bind_safe hp (fun b => map_safe ih (List.cons b))

def many (p : Parser α β) : Nat → List α → List β × List α
  | 0, input => ([],input)
  | n+1, input => match p input with
      | none => ([],input)
      | some (b,middle) =>
        let result := many p n middle
        (b::result.1,result.2)

theorem many_safe {p : Parser α β} (hp : Safe p) (n : Nat) (input : List α) :
    ∃ consumed, input = consumed ++ (many p n input).2 := by
  induction n generalizing input with
  | zero => exact ⟨[],rfl⟩
  | succ n ih =>
    cases h : p input with
    | none => exact ⟨[],by simp [many,h]⟩
    | some result =>
      rcases result with ⟨b,middle⟩
      obtain ⟨u,hu⟩ := hp input b middle h
      obtain ⟨v,hv⟩ := ih middle
      refine ⟨u++v, ?_⟩
      simp only [many,h]
      calc
        input = u ++ middle := hu
        _ = u ++ (v ++ (many p n middle).2) := congrArg (fun tail => u ++ tail) hv
        _ = (u ++ v) ++ (many p n middle).2 := (List.append_assoc _ _ _).symm

theorem many_bounds (p : Parser α β) (n : Nat) (input : List α) :
    (many p n input).1.length ≤ n ∧
      ((many p n input).1.length < n → p (many p n input).2 = none) := by
  induction n generalizing input with
  | zero => simp [many]
  | succ n ih =>
    cases h : p input with
    | none => simp [many,h]
    | some result =>
      rcases result with ⟨b,middle⟩
      have k := ih middle
      simp only [many,h,List.length_cons]
      constructor
      · omega
      · intro small
        apply k.2
        omega

theorem many_nonconsuming (b : β) (n : Nat) (input : List α) :
    many (pureP b) n input = (List.replicate n b,input) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [many,pureP,ih,List.replicate_succ]

end JonnyLean.Parsing
