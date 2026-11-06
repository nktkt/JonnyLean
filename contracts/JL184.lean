import JonnyLean.LinearAlgebra.FiniteSums

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL184 {n : Nat} (f : Fin n → Nat) :
    sum f = 0 ↔ ∀ i : Fin n, f i = 0 :=
  sum_eq_zero_iff f

theorem contract_JL184_definition (n : Nat) (f : Fin (n+1) → Nat) :
    sum f = f 0 + sum (fun i : Fin n => f i.succ) := rfl

theorem contract_JL184_concrete : sum (fun i : Fin 3 => i.val+1) = 6 := by decide

theorem contract_JL184_boundary : sum (fun i : Fin 0 => i.val) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.sum_eq_zero_iff
#print axioms contract_JL184
