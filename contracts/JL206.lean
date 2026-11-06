import JonnyLean.LinearAlgebra.DiagonalTrace

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL206 {n : Nat} (d x : Fin n → Nat) :
    act (diagonal d) x = (fun i => d i * x i) :=
  diagonal_act d x

theorem contract_JL206_definition {n : Nat} (d : Fin n → Nat) (i j : Fin n) :
    diagonal d i j = d i * (if i=j then 1 else 0) := rfl

theorem contract_JL206_concrete : trace (diagonal (fun i : Fin 3 => i.val+1)) = 6 := by decide

theorem contract_JL206_boundary : trace (fun i j : Fin 0 => i.val+j.val) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.diagonal_act
#print axioms contract_JL206
