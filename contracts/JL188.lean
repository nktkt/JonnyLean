import JonnyLean.LinearAlgebra.Vectors

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL188 {n : Nat} (x x' y y' : Fin n → Nat) (hx : ∀ i, x i ≤ x' i) (hy : ∀ i, y i ≤ y' i) :
    dot x y ≤ dot x' y' :=
  dot_mono x x' y y' hx hy

theorem contract_JL188_definition {n : Nat} (x y : Fin n → Nat) :
    dot x y = sum (fun i => x i * y i) := rfl

theorem contract_JL188_concrete : dot (fun i : Fin 2 => i.val+1) (fun i => i.val+1) = 5 := by decide

theorem contract_JL188_boundary : dot (fun i : Fin 0 => i.val) (fun i => i.val) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.dot_mono
#print axioms contract_JL188
