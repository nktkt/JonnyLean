import JonnyLean.Imperative.Expressions

namespace JonnyLean.Contracts.JL266
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (e : AExp) (s t : State), (∀ x ∈ AExp.vars e, s x = t x) → AExp.eval s e = AExp.eval t e := by
  exact AExp.eval_agrees

theorem definition_check : ∀ (s : State) (a b : AExp), AExp.eval s (.sub a b) = AExp.eval s a - AExp.eval s b := by
  intro s a b; rfl

theorem boundary_check : AExp.vars (.sub (.var 0) (.mul (.lit 3) (.var 0))) = [0, 0] := by
  rfl

end JonnyLean.Contracts.JL266

#print axioms JonnyLean.Imperative.AExp.eval_agrees
#print axioms JonnyLean.Contracts.JL266.contract
