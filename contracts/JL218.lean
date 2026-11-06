import JonnyLean.LinearAlgebra.OuterProducts

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL218 {m n p : Nat} (x : Fin m → Nat) (y z : Fin n → Nat) (w : Fin p → Nat) :
    mulMat (outer x y) (outer z w) = scaleMat (dot y z) (outer x w) :=
  outer_mul x y z w

theorem contract_JL218_definition {m n : Nat} (x : Fin m → Nat) (y : Fin n → Nat) (i : Fin m) (j : Fin n) :
    outer x y i j = x i * y j := rfl

theorem contract_JL218_concrete : trace (outer (fun i : Fin 2 => i.val+1) (fun i => i.val+1)) = 5 := by decide

theorem contract_JL218_boundary : trace (outer (fun i : Fin 0 => i.val) (fun i => i.val)) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.outer_mul
#print axioms contract_JL218
