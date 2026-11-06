import JonnyLean.Arithmetic.Product

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL067 (xs : List Nat) : product xs = 0 ↔ 0 ∈ xs :=
  product_eq_zero xs

theorem contract_JL067_definition (a : Nat) (xs : List Nat) : product (a::xs) = a*product xs := rfl

theorem contract_JL067_boundary1 : product [] = 1 := by decide

theorem contract_JL067_boundary2 : product [3,0,7] = 0 := by decide

#print axioms JonnyLean.Arithmetic.product_eq_zero
#print axioms contract_JL067
