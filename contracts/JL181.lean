import JonnyLean.LinearAlgebra.FiniteSums

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL181 {n : Nat} (a b : Nat) (f g : Fin n → Nat) :
    sum (fun i => a * f i + b * g i) = a * sum f + b * sum g :=
  sum_linear a b f g

theorem contract_JL181_definition (n : Nat) (f : Fin (n+1) → Nat) :
    sum f = f 0 + sum (fun i : Fin n => f i.succ) := rfl

theorem contract_JL181_concrete : sum (fun i : Fin 3 => i.val+1) = 6 := by decide

theorem contract_JL181_boundary : sum (fun i : Fin 0 => i.val) = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.sum_linear
#print axioms contract_JL181
