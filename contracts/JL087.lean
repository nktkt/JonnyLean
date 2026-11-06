import JonnyLean.Polynomials.Power

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL087 (p : Polynomial) (n x : Nat) :
    evaluate (power p n) x = (evaluate p x)^n :=
  evaluate_power p n x

theorem contract_JL087_definition (p : Polynomial) (n : Nat) : power p (n+1) = multiply (power p n) p := rfl

theorem contract_JL087_boundary1 : evaluate (power [] 0) 0 = 1 := by decide

theorem contract_JL087_boundary2 : evaluate (power [1,1] 3) 2 = 27 := by decide

#print axioms JonnyLean.Polynomials.evaluate_power
#print axioms contract_JL087
