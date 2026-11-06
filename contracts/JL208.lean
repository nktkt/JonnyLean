import JonnyLean.LinearAlgebra.DiagonalTrace

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL208 {m n : Nat} (A : Fin m → Fin n → Nat) (B : Fin n → Fin m → Nat) :
    trace (mulMat A B) = trace (mulMat B A) :=
  trace_mul_cyclic A B

theorem contract_JL208_definition {n : Nat} (d : Fin n → Nat) (i j : Fin n) :
    diagonal d i j = d i * (if i=j then 1 else 0) := rfl

theorem contract_JL208_concrete : trace (diagonal (fun i : Fin 3 => i.val+1)) = 6 := by decide

theorem contract_JL208_boundary : trace (fun i j : Fin 0 => i.val+j.val) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.trace_mul_cyclic
#print axioms contract_JL208
