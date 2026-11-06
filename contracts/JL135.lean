import JonnyLean.VerifiedPrograms.MachineSpecifications

namespace JonnyLean.Contracts.JL135

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (e : Expr) (depth : Nat), verifiedDepth (bytecode e) depth = some (depth + 1) := by
  intro e depth
  simpa only [verifiedDepth_matches, bytecode_matches] using Machine.check_compile e depth

theorem zero_initial_depth : verifiedDepth (bytecode (.add (.var 0) (.lit 1))) 0 = some 1 := rfl

theorem nonzero_initial_depth : verifiedDepth (bytecode (.mul (.lit 2) (.lit 3))) 7 = some 8 := rfl

end JonnyLean.Contracts.JL135

#print axioms JonnyLean.VerifiedPrograms.Machine.check_compile
#print axioms JonnyLean.Contracts.JL135.contract
