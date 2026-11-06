import JonnyLean.Arithmetic.ProductOrder

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL077 (c : Nat) (xs : List Nat) (h : ∀ a ∈ xs, a ≤ c) :
    product xs ≤ c^xs.length :=
  product_bound c xs h

theorem contract_JL077_definition (xs ys : List Nat) : product (xs++ys) = product xs*product ys := product_append xs ys

theorem contract_JL077_boundary1 : product [2,3,4] ≤ (4:Nat)^3 := by decide

theorem contract_JL077_boundary2 : product (([2,0,7] : List Nat).reverse) = 0 := by decide

#print axioms JonnyLean.Arithmetic.product_bound
#print axioms contract_JL077
