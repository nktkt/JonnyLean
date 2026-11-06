import JonnyLean.LinearAlgebra.Powers

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL216 {n : Nat} (d : Fin n → Nat) (k : Nat) :
    matPow (diagonal d) k = diagonal (fun i => d i ^ k) :=
  matPow_diagonal d k

theorem contract_JL216_definition {n : Nat} (A : Fin n → Fin n → Nat) (k : Nat) :
    matPow A (k+1) = mulMat A (matPow A k) := rfl

theorem contract_JL216_concrete : matPow (fun i j : Fin 2 => i.val+j.val+1) 2 1 1 = 13 := by decide

theorem contract_JL216_boundary : matPow (fun _ _ : Fin 1 => 0) 0 0 0 = 1 := by decide

#print axioms JonnyLean.LinearAlgebra.matPow_diagonal
#print axioms contract_JL216
