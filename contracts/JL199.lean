import JonnyLean.LinearAlgebra.Multiplication

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL199 {m n p : Nat} (A A' : Fin m → Fin n → Nat) (B B' : Fin n → Fin p → Nat) (hA : ∀ i j, A i j ≤ A' i j) (hB : ∀ j k, B j k ≤ B' j k) :
    ∀ i k, mulMat A B i k ≤ mulMat A' B' i k :=
  mulMat_mono A A' B B' hA hB

theorem contract_JL199_definition {m n p : Nat} (A : Fin m → Fin n → Nat) (B : Fin n → Fin p → Nat) (i : Fin m) (k : Fin p) :
    mulMat A B i k = sum (fun j : Fin n => A i j * B j k) := rfl

theorem contract_JL199_concrete : mulMat (fun i j : Fin 2 => i.val+j.val+1) (fun i j : Fin 2 => i.val+j.val+1) 1 1 = 13 := by decide

theorem contract_JL199_boundary : mulMat (fun (_ : Fin 1) (j : Fin 0) => j.val) (fun (i : Fin 0) (_ : Fin 1) => i.val) 0 0 = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.mulMat_mono
#print axioms contract_JL199
