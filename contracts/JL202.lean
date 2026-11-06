import JonnyLean.LinearAlgebra.Actions

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL202 {m n : Nat} (A : Fin m → Fin n → Nat) (a b : Nat) (x y : Fin n → Nat) :
    act A (vadd (scale a x) (scale b y)) = vadd (scale a (act A x)) (scale b (act A y)) :=
  act_linear A a b x y

theorem contract_JL202_definition {m n : Nat} (A : Fin m → Fin n → Nat) (x : Fin n → Nat) (i : Fin m) :
    act A x i = sum (fun j => A i j * x j) := rfl

theorem contract_JL202_concrete : act (fun i j : Fin 2 => i.val+j.val+1) (fun j => j.val+1) 1 = 8 := by decide

theorem contract_JL202_boundary : act (fun (_ : Fin 1) (j : Fin 0) => j.val) (fun i => i.val) 0 = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.act_linear
#print axioms contract_JL202
