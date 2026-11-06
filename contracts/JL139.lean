import JonnyLean.VerifiedPrograms.MachineSpecifications

namespace JonnyLean.Contracts.JL139

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (e : Expr) (stack : List Expr), reconstruction (bytecode e) stack = some (e :: stack) := by
  intro e stack
  simpa only [reconstruction_matches, bytecode_matches] using Machine.decompile_compile e stack

theorem literal_roundtrip : reconstruction (bytecode (.lit 8)) [] = some [.lit 8] := rfl

theorem syntax_not_evaluation : reconstruction (bytecode (.add (.lit 1) (.lit 2))) [] = some [.add (.lit 1) (.lit 2)] := rfl

end JonnyLean.Contracts.JL139

#print axioms JonnyLean.VerifiedPrograms.Machine.decompile_compile
#print axioms JonnyLean.Contracts.JL139.contract
