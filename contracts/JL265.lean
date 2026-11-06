import JonnyLean.Imperative.Expressions

namespace JonnyLean.Contracts.JL265
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (s : State) (x : Nat) (r e : AExp), AExp.eval s (AExp.subst x r e) = AExp.eval (update s x (AExp.eval s r)) e := by
  exact AExp.eval_subst

theorem definition_check : ∀ (s : State) (a b : AExp), AExp.eval s (.sub a b) = AExp.eval s a - AExp.eval s b := by
  intro s a b; rfl

theorem boundary_check : AExp.eval (fun _ => 4) (AExp.subst 0 (.add (.var 0) (.lit 1)) (.sub (.var 0) (.lit 9))) = 0 := by
  rfl

end JonnyLean.Contracts.JL265

#print axioms JonnyLean.Imperative.AExp.eval_subst
#print axioms JonnyLean.Contracts.JL265.contract
