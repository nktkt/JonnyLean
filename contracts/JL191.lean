import JonnyLean.LinearAlgebra.Matrices

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL191 {m n : Nat} (a b : Nat) (A B : Fin m → Fin n → Nat) :
    scaleMat a (addMat A B) = addMat (scaleMat a A) (scaleMat a B) ∧ scaleMat (a+b) A = addMat (scaleMat a A) (scaleMat b A) ∧ scaleMat a (scaleMat b A) = scaleMat (a*b) A ∧ scaleMat 1 A = A :=
  matrix_semimodule_laws a b A B

theorem contract_JL191_definition {m n : Nat} (A : Fin m → Fin n → Nat) (i : Fin n) (j : Fin m) :
    transpose A i j = A j i := rfl

theorem contract_JL191_concrete : transpose (fun i j : Fin 2 => i.val+2*j.val) 1 0 = 2 := by decide

theorem contract_JL191_boundary : identity 1 0 0 = 1 := by decide

#print axioms JonnyLean.LinearAlgebra.matrix_semimodule_laws
#print axioms contract_JL191
