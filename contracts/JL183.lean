import JonnyLean.LinearAlgebra.FiniteSums

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL183 {n : Nat} (k : Fin n) (f : Fin n → Nat) :
    sum (fun i => (if k = i then 1 else 0) * f i) = f k :=
  sum_delta k f

theorem contract_JL183_definition (n : Nat) (f : Fin (n+1) → Nat) :
    sum f = f 0 + sum (fun i : Fin n => f i.succ) := rfl

theorem contract_JL183_concrete : sum (fun i : Fin 3 => i.val+1) = 6 := by decide

theorem contract_JL183_boundary : sum (fun i : Fin 0 => i.val) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.sum_delta
#print axioms contract_JL183
