import JonnyLean.Arithmetic.GcdList

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL062 (d : Nat) (xs : List Nat) :
    d ∣ listGcd xs ↔ ∀ a ∈ xs, d ∣ a :=
  dvd_listGcd d xs

theorem contract_JL062_definition (a : Nat) (xs : List Nat) : listGcd (a::xs) = Nat.gcd a (listGcd xs) := rfl

theorem contract_JL062_boundary1 : listGcd [] = 0 := by decide

theorem contract_JL062_boundary2 : listGcd [0,18,30,42] = 6 := by decide

#print axioms JonnyLean.Arithmetic.dvd_listGcd
#print axioms contract_JL062
