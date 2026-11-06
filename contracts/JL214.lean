import JonnyLean.LinearAlgebra.Powers

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL214 {n : Nat} (A : Fin n → Fin n → Nat) (k l : Nat) :
    mulMat (matPow A k) (matPow A l) = mulMat (matPow A l) (matPow A k) :=
  matPow_factors_commute A k l

theorem contract_JL214_definition {n : Nat} (A : Fin n → Fin n → Nat) (k : Nat) :
    matPow A (k+1) = mulMat A (matPow A k) := rfl

theorem contract_JL214_concrete : matPow (fun i j : Fin 2 => i.val+j.val+1) 2 1 1 = 13 := by decide

theorem contract_JL214_boundary : matPow (fun _ _ : Fin 1 => 0) 0 0 0 = 1 := by decide

#print axioms JonnyLean.LinearAlgebra.matPow_factors_commute
#print axioms contract_JL214
