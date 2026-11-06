import JonnyLean.Imperative.State

namespace JonnyLean.Imperative

inductive AExp where
  | lit : Nat → AExp
  | var : Nat → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  deriving DecidableEq, Repr

namespace AExp

def eval (s : State) : AExp → Nat
  | .lit n => n
  | .var x => s x
  | .add a b => eval s a + eval s b
  | .sub a b => eval s a - eval s b
  | .mul a b => eval s a * eval s b

def vars : AExp → List Nat
  | .lit _ => []
  | .var x => [x]
  | .add a b | .sub a b | .mul a b => vars a ++ vars b

def subst (x : Nat) (r : AExp) : AExp → AExp
  | .lit n => .lit n
  | .var y => if y = x then r else .var y
  | .add a b => .add (subst x r a) (subst x r b)
  | .sub a b => .sub (subst x r a) (subst x r b)
  | .mul a b => .mul (subst x r a) (subst x r b)

theorem eval_subst (s : State) (x : Nat) (r e : AExp) :
    eval s (subst x r e) = eval (update s x (eval s r)) e := by
  induction e with
  | lit => rfl
  | var y => simp [subst, eval, update]; split <;> rfl
  | add a b ha hb => simp [subst, eval, ha, hb]
  | sub a b ha hb => simp [subst, eval, ha, hb]
  | mul a b ha hb => simp [subst, eval, ha, hb]

theorem eval_agrees (e : AExp) (s t : State) (h : Agrees e.vars s t) : eval s e = eval t e := by
  induction e with
  | lit => rfl
  | var x => exact h x (by simp [vars])
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    have h₁ : Agrees a.vars s t := fun x hx => h x (List.mem_append_left _ hx)
    have h₂ : Agrees b.vars s t := fun x hx => h x (List.mem_append_right _ hx)
    simp [eval, ha h₁, hb h₂]

theorem eval_update_fresh (e : AExp) (s : State) (x n : Nat) (h : x ∉ e.vars) :
    eval (update s x n) e = eval s e := by
  apply eval_agrees
  intro y hy
  exact update_other s x y n (fun heq => h (heq ▸ hy))

theorem subst_self (x : Nat) (e : AExp) : subst x (.var x) e = e := by
  induction e with
  | lit => rfl
  | var y => simp [subst]; exact fun h => h.symm
  | add a b ha hb | sub a b ha hb | mul a b ha hb => simp [subst, ha, hb]

end AExp

inductive BExp where
  | truth : Bool → BExp
  | eq : AExp → AExp → BExp
  | le : AExp → AExp → BExp
  | not : BExp → BExp
  | and : BExp → BExp → BExp
  deriving DecidableEq, Repr

namespace BExp

def eval (s : State) : BExp → Bool
  | .truth b => b
  | .eq a b => decide (a.eval s = b.eval s)
  | .le a b => decide (a.eval s ≤ b.eval s)
  | .not b => !(eval s b)
  | .and a b => eval s a && eval s b

def vars : BExp → List Nat
  | .truth _ => []
  | .eq a b | .le a b => a.vars ++ b.vars
  | .not b => vars b
  | .and a b => vars a ++ vars b

def subst (x : Nat) (r : AExp) : BExp → BExp
  | .truth b => .truth b
  | .eq a b => .eq (AExp.subst x r a) (AExp.subst x r b)
  | .le a b => .le (AExp.subst x r a) (AExp.subst x r b)
  | .not b => .not (subst x r b)
  | .and a b => .and (subst x r a) (subst x r b)

theorem eval_subst (s : State) (x : Nat) (r : AExp) (b : BExp) :
    eval s (subst x r b) = eval (update s x (r.eval s)) b := by
  induction b <;> simp_all [subst, eval, AExp.eval_subst]

theorem eval_agrees (b : BExp) (s t : State) (h : Agrees b.vars s t) : eval s b = eval t b := by
  induction b with
  | truth => rfl
  | eq a b | le a b =>
    have ha : a.eval s = a.eval t := AExp.eval_agrees a s t (fun x hx => h x (List.mem_append_left _ hx))
    have hb : b.eval s = b.eval t := AExp.eval_agrees b s t (fun x hx => h x (List.mem_append_right _ hx))
    simp [eval, ha, hb]
  | not b ih => simp [eval, ih h]
  | and a b ha hb =>
    have h₁ : Agrees a.vars s t := fun x hx => h x (List.mem_append_left _ hx)
    have h₂ : Agrees b.vars s t := fun x hx => h x (List.mem_append_right _ hx)
    simp [eval, ha h₁, hb h₂]

theorem eval_update_fresh (b : BExp) (s : State) (x n : Nat) (h : x ∉ b.vars) :
    eval (update s x n) b = eval s b := by
  apply eval_agrees
  intro y hy
  exact update_other s x y n (fun heq => h (heq ▸ hy))

end BExp
end JonnyLean.Imperative
