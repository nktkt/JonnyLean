import JonnyLean.LinearAlgebra.Matrices

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL192 {m n : Nat} (A : Fin m → Fin n → Nat) :
    transpose (transpose A) = A :=
  transpose_transpose A

theorem contract_JL192_definition {m n : Nat} (A : Fin m → Fin n → Nat) (i : Fin n) (j : Fin m) :
    transpose A i j = A j i := rfl

theorem contract_JL192_concrete : transpose (fun i j : Fin 2 => i.val+2*j.val) 1 0 = 2 := by decide

theorem contract_JL192_boundary : identity 1 0 0 = 1 := by decide

#print axioms JonnyLean.LinearAlgebra.transpose_transpose
#print axioms contract_JL192
