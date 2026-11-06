import JonnyLean.Imperative.Semantics

namespace JonnyLean.Contracts.JL272
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (a b c : Cmd) (s t : State), Exec (.seq (.seq a b) c) s t ↔ Exec (.seq a (.seq b c)) s t := by
  exact exec_seq_assoc

theorem definition_check : ∀ (s : State) (x : Nat) (e : AExp), Exec (.assign x e) s (update s x (AExp.eval s e)) := by
  exact Exec.assign

theorem boundary_check : Exec (.seq (.seq .skip .skip) .skip) (fun _ => 0) (fun _ => 0) := by
  exact .seq (.seq (.skip _) (.skip _)) (.skip _)

end JonnyLean.Contracts.JL272

#print axioms JonnyLean.Imperative.exec_seq_assoc
#print axioms JonnyLean.Contracts.JL272.contract
