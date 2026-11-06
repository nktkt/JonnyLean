import JonnyLean.Arithmetic.ModularPower

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL072 (m a n : Nat) : modularPower m a n = a^n % m :=
  modularPower_correct m a n

theorem contract_JL072_definition (m a n : Nat) : modularPower m a (n+1) = (modularPower m a n*a)%m := rfl

theorem contract_JL072_boundary1 : modularPower 0 3 4 = 81 := by decide

theorem contract_JL072_boundary2 : modularPower 5 3 4 = 1 := by decide

#print axioms JonnyLean.Arithmetic.modularPower_correct
#print axioms contract_JL072
