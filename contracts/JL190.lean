import JonnyLean.LinearAlgebra.Vectors

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL190 {n : Nat} (x : Fin n → Nat) :
    (fun j => sum (fun i => x i * basis i j)) = x :=
  basis_reconstruction x

theorem contract_JL190_definition {n : Nat} (x y : Fin n → Nat) :
    dot x y = sum (fun i => x i * y i) := rfl

theorem contract_JL190_concrete : dot (fun i : Fin 2 => i.val+1) (fun i => i.val+1) = 5 := by decide

theorem contract_JL190_boundary : dot (fun i : Fin 0 => i.val) (fun i => i.val) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.basis_reconstruction
#print axioms contract_JL190
