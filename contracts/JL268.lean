import JonnyLean.Imperative.Expressions

namespace JonnyLean.Contracts.JL268
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (s : State) (x : Nat) (r : AExp) (b : BExp), BExp.eval s (BExp.subst x r b) = BExp.eval (update s x (AExp.eval s r)) b := by
  exact BExp.eval_subst

theorem definition_check : ∀ (s : State) (a b : AExp), AExp.eval s (.sub a b) = AExp.eval s a - AExp.eval s b := by
  intro s a b; rfl

theorem boundary_check : BExp.eval (fun _ => 0) (BExp.subst 0 (.lit 2) (.le (.lit 1) (.var 0))) = true := by
  rfl

end JonnyLean.Contracts.JL268

#print axioms JonnyLean.Imperative.BExp.eval_subst
#print axioms JonnyLean.Contracts.JL268.contract
