import JonnyLean.Imperative.Expressions

namespace JonnyLean.Contracts.JL270
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (b : BExp) (s : State) (x n : Nat), x ∉ BExp.vars b → BExp.eval (update s x n) b = BExp.eval s b := by
  exact BExp.eval_update_fresh

theorem definition_check : ∀ (s : State) (a b : AExp), AExp.eval s (.sub a b) = AExp.eval s a - AExp.eval s b := by
  intro s a b; rfl

theorem boundary_check : BExp.eval (update (fun _ => 0) 5 9) (.not (.le (.lit 1) (.var 0))) = true := by
  rfl

end JonnyLean.Contracts.JL270

#print axioms JonnyLean.Imperative.BExp.eval_update_fresh
#print axioms JonnyLean.Contracts.JL270.contract
