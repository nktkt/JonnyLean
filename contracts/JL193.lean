import JonnyLean.LinearAlgebra.Multiplication

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL193 {m n p : Nat} (A : Fin m → Fin n → Nat) (B C : Fin n → Fin p → Nat) :
    mulMat A (addMat B C) = addMat (mulMat A B) (mulMat A C) :=
  mulMat_add_right A B C

theorem contract_JL193_definition {m n p : Nat} (A : Fin m → Fin n → Nat) (B : Fin n → Fin p → Nat) (i : Fin m) (k : Fin p) :
    mulMat A B i k = sum (fun j : Fin n => A i j * B j k) := rfl

theorem contract_JL193_concrete : mulMat (fun i j : Fin 2 => i.val+j.val+1) (fun i j : Fin 2 => i.val+j.val+1) 1 1 = 13 := by decide

theorem contract_JL193_boundary : mulMat (fun (_ : Fin 1) (j : Fin 0) => j.val) (fun (i : Fin 0) (_ : Fin 1) => i.val) 0 0 = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.mulMat_add_right
#print axioms contract_JL193
