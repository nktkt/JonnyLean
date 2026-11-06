import JonnyLean.LinearAlgebra.OuterProducts

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL220 {n : Nat} (x y : Fin n → Nat) (h : dot y x = 1) :
    mulMat (outer x y) (outer x y) = outer x y :=
  outer_idempotent_of_dot_one x y h

theorem contract_JL220_definition {m n : Nat} (x : Fin m → Nat) (y : Fin n → Nat) (i : Fin m) (j : Fin n) :
    outer x y i j = x i * y j := rfl

theorem contract_JL220_concrete : trace (outer (fun i : Fin 2 => i.val+1) (fun i => i.val+1)) = 5 := by decide

theorem contract_JL220_boundary : trace (outer (fun i : Fin 0 => i.val) (fun i => i.val)) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.outer_idempotent_of_dot_one
#print axioms contract_JL220

theorem contract_JL220_projection_example :
    let x : Fin 2 → Nat := fun i => if i.val = 0 then 1 else 0
    let y : Fin 2 → Nat := fun i => i.val + 1
    dot y x = 1 ∧ mulMat (outer x y) (outer x y) = outer x y := by
  dsimp only
  have h : dot (fun i : Fin 2 => i.val + 1) (fun i : Fin 2 => if i.val = 0 then 1 else 0) = 1 := by decide
  exact ⟨h, outer_idempotent_of_dot_one _ _ h⟩
