import JonnyLean.LinearAlgebra.OuterProducts

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL217 {m n : Nat} (x : Fin m → Nat) (y z : Fin n → Nat) :
    act (outer x y) z = scale (dot y z) x :=
  outer_action x y z

theorem contract_JL217_definition {m n : Nat} (x : Fin m → Nat) (y : Fin n → Nat) (i : Fin m) (j : Fin n) :
    outer x y i j = x i * y j := rfl

theorem contract_JL217_concrete : trace (outer (fun i : Fin 2 => i.val+1) (fun i => i.val+1)) = 5 := by decide

theorem contract_JL217_boundary : trace (outer (fun i : Fin 0 => i.val) (fun i => i.val)) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.outer_action
#print axioms contract_JL217
