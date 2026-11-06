import JonnyLean.Arithmetic.CoprimeProduct

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL068 (a : Nat) (xs : List Nat) :
    Nat.gcd a (product xs) = 1 ↔ ∀ b ∈ xs, Nat.gcd a b = 1 :=
  gcd_product_eq_one_iff a xs

theorem contract_JL068_definition (a : Nat) : Nat.gcd a (product []) = 1 := by simp [product]

theorem contract_JL068_boundary1 : Nat.gcd 0 (product []) = 1 := by decide

theorem contract_JL068_boundary2 : Nat.gcd 5 (product [6,7,9]) = 1 := by decide

#print axioms JonnyLean.Arithmetic.gcd_product_eq_one_iff
#print axioms contract_JL068
