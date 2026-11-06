import JonnyLean.Counting.Dependent
namespace JonnyLean.Counting

 def natProduct : List Nat → Nat
  | [] => 1
  | n :: ns => n * natProduct ns

def choices : List (List α) → List (List α)
  | [] => [[]]
  | xs :: xss => xs.flatMap (fun x => (choices xss).map (fun w => x :: w))

theorem length_choices (xss : List (List α)) :
    (choices xss).length = natProduct (xss.map List.length) := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
    change (xs.flatMap (fun x => (choices xss).map (fun w => x :: w))).length = _
    have h : ∀ xs : List α, (xs.flatMap (fun x => (choices xss).map (fun w => x :: w))).length =
        xs.length * (choices xss).length := by
      intro ys
      induction ys with
      | nil => simp
      | cons y ys hy => simp [hy, Nat.add_mul, Nat.add_comm]
    rw [h, ih]
    rfl

def Compatible : List α → List (List α) → Prop
  | [], [] => True
  | a :: w, xs :: xss => a ∈ xs ∧ Compatible w xss
  | _, _ => False

theorem mem_choices {xss : List (List α)} {w : List α} :
    w ∈ choices xss ↔ Compatible w xss := by
  induction xss generalizing w with
  | nil => cases w <;> simp [choices, Compatible]
  | cons xs xss ih =>
    cases w with
    | nil => simp [choices, Compatible]
    | cons a w => simp [choices, Compatible, ih]

theorem choice_length {xss : List (List α)} {w : List α} (h : w ∈ choices xss) :
    w.length = xss.length := by
  have hc := mem_choices.mp h
  clear h
  induction xss generalizing w with
  | nil => cases w <;> simp [Compatible] at hc ⊢
  | cons xs xss ih =>
    cases w with
    | nil => exact False.elim hc
    | cons a w => exact congrArg Nat.succ (ih hc.2)

theorem choices_empty_coordinate (xss : List (List α)) : choices ([] :: xss) = [] := rfl
end JonnyLean.Counting
