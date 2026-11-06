import JonnyLean.Imperative.Semantics

namespace JonnyLean.Contracts.JL274
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (c : Cmd) (s t : State), Exec c s t → ∀ x, x ∉ Cmd.writes c → t x = s x := by
  intro c s t h x hx
  exact exec_preserves h x hx

theorem definition_check : ∀ (s : State) (x : Nat) (e : AExp), Exec (.assign x e) s (update s x (AExp.eval s e)) := by
  exact Exec.assign

theorem boundary_check : Cmd.writes (.ite (.truth false) (.assign 1 (.lit 2)) (.assign 3 (.lit 4))) = [1,3] := by
  rfl

end JonnyLean.Contracts.JL274

#print axioms JonnyLean.Imperative.exec_preserves
#print axioms JonnyLean.Contracts.JL274.contract
