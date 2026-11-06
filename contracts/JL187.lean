import JonnyLean.LinearAlgebra.Vectors

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL187 {n : Nat} (x : Fin n → Nat) :
    dot x x = 0 ↔ x = (fun _ => 0) :=
  dot_self_zero_iff x

theorem contract_JL187_definition {n : Nat} (x y : Fin n → Nat) :
    dot x y = sum (fun i => x i * y i) := rfl

theorem contract_JL187_concrete : dot (fun i : Fin 2 => i.val+1) (fun i => i.val+1) = 5 := by decide

theorem contract_JL187_boundary : dot (fun i : Fin 0 => i.val) (fun i => i.val) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.dot_self_zero_iff
#print axioms contract_JL187
