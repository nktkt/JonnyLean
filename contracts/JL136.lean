import JonnyLean.VerifiedPrograms.MachineSpecifications

namespace JonnyLean.Contracts.JL136

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (env : Nat → Nat) (e : Expr) (stack : List Nat), execution env (bytecode (Expr.optimize e)) stack = execution env (bytecode e) stack := by
  intro env e stack
  simpa only [execution_matches, bytecode_matches] using Machine.execute_optimized_compile env e stack

theorem eliminated_load : bytecode (Expr.optimize (.mul (.lit 0) (.var 99))) = [.push 0] := rfl

theorem result_preserved : execution id (bytecode (Expr.optimize (.add (.lit 0) (.var 3)))) [7] = some [3, 7] := rfl

end JonnyLean.Contracts.JL136

#print axioms JonnyLean.VerifiedPrograms.Machine.execute_optimized_compile
#print axioms JonnyLean.Contracts.JL136.contract
