import JonnyLean.Imperative.Expressions

namespace JonnyLean.Contracts.JL267
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (e : AExp) (s : State) (x n : Nat), x ∉ AExp.vars e → AExp.eval (update s x n) e = AExp.eval s e := by
  exact AExp.eval_update_fresh

theorem definition_check : ∀ (s : State) (a b : AExp), AExp.eval s (.sub a b) = AExp.eval s a - AExp.eval s b := by
  intro s a b; rfl

theorem boundary_check : AExp.eval (update (fun _ => 5) 8 100) (.sub (.var 0) (.lit 7)) = 0 := by
  rfl

end JonnyLean.Contracts.JL267

#print axioms JonnyLean.Imperative.AExp.eval_update_fresh
#print axioms JonnyLean.Contracts.JL267.contract
