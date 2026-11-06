import JonnyLean.Imperative.Semantics

namespace JonnyLean.Contracts.JL273
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (b : BExp) (c : Cmd) (s t : State), Exec (.while b c) s t ↔ Exec (.ite b (.seq c (.while b c)) .skip) s t := by
  exact exec_while_unroll

theorem definition_check : ∀ (s : State) (x : Nat) (e : AExp), Exec (.assign x e) s (update s x (AExp.eval s e)) := by
  exact Exec.assign

theorem boundary_check : Exec (.while (.truth false) (.assign 0 (.lit 9))) (fun _ => 0) (fun _ => 0) := by
  exact .whileFalse rfl

end JonnyLean.Contracts.JL273

#print axioms JonnyLean.Imperative.exec_while_unroll
#print axioms JonnyLean.Contracts.JL273.contract
