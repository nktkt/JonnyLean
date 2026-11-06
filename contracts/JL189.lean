import JonnyLean.LinearAlgebra.Vectors

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL189 {n : Nat} (x y : Fin n → Nat) (a b : Nat) (hx : ∀ i, x i ≤ a) (hy : ∀ i, y i ≤ b) :
    dot x y ≤ n * (a*b) :=
  dot_bound x y a b hx hy

theorem contract_JL189_definition {n : Nat} (x y : Fin n → Nat) :
    dot x y = sum (fun i => x i * y i) := rfl

theorem contract_JL189_concrete : dot (fun i : Fin 2 => i.val+1) (fun i => i.val+1) = 5 := by decide

theorem contract_JL189_boundary : dot (fun i : Fin 0 => i.val) (fun i => i.val) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.dot_bound
#print axioms contract_JL189
