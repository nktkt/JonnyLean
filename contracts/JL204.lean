import JonnyLean.LinearAlgebra.Actions

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL204 {m n : Nat} (A B : Fin m → Fin n → Nat) (h : ∀ j, act A (basis j) = act B (basis j)) :
    A = B :=
  matrix_eq_of_basis_actions A B h

theorem contract_JL204_definition {m n : Nat} (A : Fin m → Fin n → Nat) (x : Fin n → Nat) (i : Fin m) :
    act A x i = sum (fun j => A i j * x j) := rfl

theorem contract_JL204_concrete : act (fun i j : Fin 2 => i.val+j.val+1) (fun j => j.val+1) 1 = 8 := by decide

theorem contract_JL204_boundary : act (fun (_ : Fin 1) (j : Fin 0) => j.val) (fun i => i.val) 0 = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.matrix_eq_of_basis_actions
#print axioms contract_JL204
