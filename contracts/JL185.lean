import JonnyLean.LinearAlgebra.Vectors

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL185 {n : Nat} (a b : Nat) (u v x y : Fin n → Nat) :
    dot (vadd (scale a u) v) (vadd (scale b x) y) = a*b*dot u x + a*dot u y + b*dot v x + dot v y :=
  dot_bilinear a b u v x y

theorem contract_JL185_definition {n : Nat} (x y : Fin n → Nat) :
    dot x y = sum (fun i => x i * y i) := rfl

theorem contract_JL185_concrete : dot (fun i : Fin 2 => i.val+1) (fun i => i.val+1) = 5 := by decide

theorem contract_JL185_boundary : dot (fun i : Fin 0 => i.val) (fun i => i.val) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.dot_bilinear
#print axioms contract_JL185
