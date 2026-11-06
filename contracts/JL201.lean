import JonnyLean.LinearAlgebra.Actions

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL201 {m n p : Nat} (A : Fin m → Fin n → Nat) (B : Fin n → Fin p → Nat) (x : Fin p → Nat) :
    act (mulMat A B) x = act A (act B x) :=
  act_comp A B x

theorem contract_JL201_definition {m n : Nat} (A : Fin m → Fin n → Nat) (x : Fin n → Nat) (i : Fin m) :
    act A x i = sum (fun j => A i j * x j) := rfl

theorem contract_JL201_concrete : act (fun i j : Fin 2 => i.val+j.val+1) (fun j => j.val+1) 1 = 8 := by decide

theorem contract_JL201_boundary : act (fun (_ : Fin 1) (j : Fin 0) => j.val) (fun i => i.val) 0 = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.act_comp
#print axioms contract_JL201
