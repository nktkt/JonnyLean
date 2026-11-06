import JonnyLean.VerifiedPrograms.MachineSpecifications

namespace JonnyLean.Contracts.JL138

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (env : Nat → Nat) (code : List Instr) (stack result suffix : List Nat), execution env code stack = some result → execution env code (stack ++ suffix) = some (result ++ suffix) := by
  intro env code stack result suffix h
  simpa only [execution_matches] using Machine.execute_frame env code stack result suffix (by simpa only [execution_matches] using h)

theorem preserved_bottom : execution id [.add] [2, 3, 99] = some [5, 99] := rfl

theorem failure_needs_premise : execution id [.add] [] = none ∧ execution id [.add] [2, 3] = some [5] := ⟨rfl, rfl⟩

end JonnyLean.Contracts.JL138

#print axioms JonnyLean.VerifiedPrograms.Machine.execute_frame
#print axioms JonnyLean.Contracts.JL138.contract
