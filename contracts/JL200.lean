import JonnyLean.LinearAlgebra.Multiplication

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL200 {m n p : Nat} (A : Fin m → Fin n → Nat) (B : Fin n → Fin p → Nat) (a b : Nat) (hA : ∀ i j, A i j ≤ a) (hB : ∀ j k, B j k ≤ b) :
    ∀ i k, mulMat A B i k ≤ n * (a*b) :=
  mulMat_bound A B a b hA hB

theorem contract_JL200_definition {m n p : Nat} (A : Fin m → Fin n → Nat) (B : Fin n → Fin p → Nat) (i : Fin m) (k : Fin p) :
    mulMat A B i k = sum (fun j : Fin n => A i j * B j k) := rfl

theorem contract_JL200_concrete : mulMat (fun i j : Fin 2 => i.val+j.val+1) (fun i j : Fin 2 => i.val+j.val+1) 1 1 = 13 := by decide

theorem contract_JL200_boundary : mulMat (fun (_ : Fin 1) (j : Fin 0) => j.val) (fun (i : Fin 0) (_ : Fin 1) => i.val) 0 0 = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.mulMat_bound
#print axioms contract_JL200
