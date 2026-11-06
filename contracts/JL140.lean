import JonnyLean.VerifiedPrograms.MachineSpecifications

namespace JonnyLean.Contracts.JL140

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (env : Nat → Nat) (code : List Instr) (stack result : List Expr), reconstruction code stack = some result → execution env code (stack.map (meaning env)) = some (result.map (meaning env)) := by
  intro env code stack result h
  have hfun : meaning env = Expr.eval env := funext (fun e => meaning_matches env e)
  rw [hfun]
  simpa only [execution_matches] using Machine.decompile_sound env code stack result (by simpa only [reconstruction_matches] using h)

theorem raw_instruction : reconstruction [.add] [.var 1, .lit 2] = some [.add (.lit 2) (.var 1)] := rfl

theorem raw_underflow : reconstruction [.mul] [.lit 2] = none := rfl

end JonnyLean.Contracts.JL140

#print axioms JonnyLean.VerifiedPrograms.Machine.decompile_sound
#print axioms JonnyLean.Contracts.JL140.contract
