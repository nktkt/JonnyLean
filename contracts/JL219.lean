import JonnyLean.LinearAlgebra.OuterProducts

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL219 {m n : Nat} (x : Fin m → Nat) (y : Fin n → Nat) :
    transpose (outer x y) = outer y x :=
  transpose_outer x y

theorem contract_JL219_definition {m n : Nat} (x : Fin m → Nat) (y : Fin n → Nat) (i : Fin m) (j : Fin n) :
    outer x y i j = x i * y j := rfl

theorem contract_JL219_concrete : trace (outer (fun i : Fin 2 => i.val+1) (fun i => i.val+1)) = 5 := by decide

theorem contract_JL219_boundary : trace (outer (fun i : Fin 0 => i.val) (fun i => i.val)) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.transpose_outer
#print axioms contract_JL219
