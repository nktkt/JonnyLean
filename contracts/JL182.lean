import JonnyLean.LinearAlgebra.FiniteSums

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL182 {m n : Nat} (f : Fin m → Fin n → Nat) :
    sum (fun i => sum (fun j => f i j)) = sum (fun j => sum (fun i => f i j)) :=
  sum_swap f

theorem contract_JL182_definition (n : Nat) (f : Fin (n+1) → Nat) :
    sum f = f 0 + sum (fun i : Fin n => f i.succ) := rfl

theorem contract_JL182_concrete : sum (fun i : Fin 3 => i.val+1) = 6 := by decide

theorem contract_JL182_boundary : sum (fun i : Fin 0 => i.val) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.sum_swap
#print axioms contract_JL182
