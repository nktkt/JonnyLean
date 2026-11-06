import JonnyLean.VerifiedPrograms.MachineSpecifications

namespace JonnyLean.Contracts.JL131

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (env : Nat → Nat) (first second : List Instr) (stack : List Nat), execution env (first ++ second) stack = (execution env first stack).bind (execution env second) := by
  intro env first second stack
  have hfun : execution env second = Machine.execute env second :=
    funext (fun s => execution_matches env second s)
  rw [hfun]
  simpa only [execution_matches] using Machine.execute_append env first second stack

theorem empty_program : execution id [] [1, 2] = some [1, 2] := rfl

theorem early_underflow : execution id [.add, .push 1] [] = none := rfl

end JonnyLean.Contracts.JL131

#print axioms JonnyLean.VerifiedPrograms.Machine.execute_append
#print axioms JonnyLean.Contracts.JL131.contract
