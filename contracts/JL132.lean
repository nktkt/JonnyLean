import JonnyLean.VerifiedPrograms.MachineSpecifications

namespace JonnyLean.Contracts.JL132

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (env : Nat → Nat) (e : Expr) (stack : List Nat), execution env (Machine.compile e) stack = some (meaning env e :: stack) := by
  intro env e stack
  simpa only [execution_matches, meaning_matches] using Machine.execute_compile env e stack

theorem literal_compiled : execution id (Machine.compile (.lit 5)) [9] = some [5, 9] := rfl

theorem mixed_compiled : execution id (Machine.compile (.mul (.var 3) (.add (.lit 2) (.lit 4)))) [] = some [18] := rfl

end JonnyLean.Contracts.JL132

#print axioms JonnyLean.VerifiedPrograms.Machine.execute_compile
#print axioms JonnyLean.Contracts.JL132.contract
