import JonnyLean.VerifiedPrograms.MachineSpecifications

namespace JonnyLean.Contracts.JL137

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (e : Expr) (tail : List Instr), Machine.compileInto e tail = bytecode e ++ tail := by
  intro e tail
  simpa only [bytecode_matches] using Machine.compileInto_spec e tail

theorem literal_with_tail : Machine.compileInto (.lit 2) [.push 3, .add] = [.push 2, .push 3, .add] := rfl

theorem empty_tail : Machine.compileInto (.var 0) [] = [.load 0] := rfl

end JonnyLean.Contracts.JL137

#print axioms JonnyLean.VerifiedPrograms.Machine.compileInto_spec
#print axioms JonnyLean.Contracts.JL137.contract
