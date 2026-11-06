import JonnyLean.VerifiedPrograms.MachineSpecifications

namespace JonnyLean.Contracts.JL134

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (env : Nat → Nat) (code : List Instr) (stack : List Nat) (depth : Nat), verifiedDepth code stack.length = some depth → ∃ result, execution env code stack = some result ∧ result.length = depth := by
  intro env code stack depth h
  simpa only [execution_matches] using Machine.check_sound env code stack depth (by simpa only [verifiedDepth_matches] using h)

theorem reject_underflow : verifiedDepth [.add] 1 = none := rfl

theorem accept_operation : verifiedDepth [.mul] 2 = some 1 := rfl

end JonnyLean.Contracts.JL134

#print axioms JonnyLean.VerifiedPrograms.Machine.check_sound
#print axioms JonnyLean.Contracts.JL134.contract
