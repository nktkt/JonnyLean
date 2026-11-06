import JonnyLean.LinearAlgebra.Actions

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL203 {m n : Nat} (A : Fin m → Fin n → Nat) (j : Fin n) :
    act A (basis j) = (fun i => A i j) :=
  act_basis A j

theorem contract_JL203_definition {m n : Nat} (A : Fin m → Fin n → Nat) (x : Fin n → Nat) (i : Fin m) :
    act A x i = sum (fun j => A i j * x j) := rfl

theorem contract_JL203_concrete : act (fun i j : Fin 2 => i.val+j.val+1) (fun j => j.val+1) 1 = 8 := by decide

theorem contract_JL203_boundary : act (fun (_ : Fin 1) (j : Fin 0) => j.val) (fun i => i.val) 0 = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.act_basis
#print axioms contract_JL203
