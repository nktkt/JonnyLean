import JonnyLean.LinearAlgebra.DiagonalTrace

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL205 {n : Nat} (d e : Fin n → Nat) :
    mulMat (diagonal d) (diagonal e) = diagonal (fun i => d i * e i) :=
  diagonal_mul d e

theorem contract_JL205_definition {n : Nat} (d : Fin n → Nat) (i j : Fin n) :
    diagonal d i j = d i * (if i=j then 1 else 0) := rfl

theorem contract_JL205_concrete : trace (diagonal (fun i : Fin 3 => i.val+1)) = 6 := by decide

theorem contract_JL205_boundary : trace (fun i j : Fin 0 => i.val+j.val) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.diagonal_mul
#print axioms contract_JL205
