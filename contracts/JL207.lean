import JonnyLean.LinearAlgebra.DiagonalTrace

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL207 {n : Nat} (a b : Nat) (A B : Fin n → Fin n → Nat) :
    trace (addMat (scaleMat a A) (scaleMat b B)) = a * trace A + b * trace B :=
  trace_linear a b A B

theorem contract_JL207_definition {n : Nat} (d : Fin n → Nat) (i j : Fin n) :
    diagonal d i j = d i * (if i=j then 1 else 0) := rfl

theorem contract_JL207_concrete : trace (diagonal (fun i : Fin 3 => i.val+1)) = 6 := by decide

theorem contract_JL207_boundary : trace (fun i j : Fin 0 => i.val+j.val) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.trace_linear
#print axioms contract_JL207
