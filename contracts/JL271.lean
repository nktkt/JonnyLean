import JonnyLean.Imperative.Semantics

namespace JonnyLean.Contracts.JL271
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (c : Cmd) (s t u : State), Exec c s t → Exec c s u → t = u := by
  intro c s t u h k
  exact exec_deterministic h k

theorem definition_check : ∀ (s : State) (x : Nat) (e : AExp), Exec (.assign x e) s (update s x (AExp.eval s e)) := by
  exact Exec.assign

theorem boundary_check : Exec (.assign 0 (.lit 2)) (fun _ => 0) (update (fun _ => 0) 0 2) := by
  exact .assign _ _ _

end JonnyLean.Contracts.JL271

#print axioms JonnyLean.Imperative.exec_deterministic
#print axioms JonnyLean.Contracts.JL271.contract
