import JonnyLean.Imperative.Expressions

namespace JonnyLean.Contracts.JL269
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (b : BExp) (s t : State), (∀ x ∈ BExp.vars b, s x = t x) → BExp.eval s b = BExp.eval t b := by
  exact BExp.eval_agrees

theorem definition_check : ∀ (s : State) (a b : AExp), AExp.eval s (.sub a b) = AExp.eval s a - AExp.eval s b := by
  intro s a b; rfl

theorem boundary_check : BExp.vars (.not (.eq (.var 3) (.var 4))) = [3,4] := by
  rfl

end JonnyLean.Contracts.JL269

#print axioms JonnyLean.Imperative.BExp.eval_agrees
#print axioms JonnyLean.Contracts.JL269.contract
