import JonnyLean.VerifiedPrograms.MachineSpecifications

namespace JonnyLean.Contracts.JL133

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ e : Expr, (bytecode e).length = syntaxSize e := by
  intro e
  simpa only [bytecode_matches, syntaxSize_matches] using Machine.compile_length e

theorem one_instruction : (bytecode (.var 9)).length = 1 := rfl

theorem three_instructions : (bytecode (.add (.lit 1) (.lit 2))).length = 3 := rfl

end JonnyLean.Contracts.JL133

#print axioms JonnyLean.VerifiedPrograms.Machine.compile_length
#print axioms JonnyLean.Contracts.JL133.contract
