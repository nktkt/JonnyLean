import JonnyLean.Polynomials.DerivativeRules

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL099 (p q : Polynomial) (x : Nat) :
    evaluate (derivative (compose p q)) x =
      evaluate (derivative p) (evaluate q x) * evaluate (derivative q) x :=
  evaluate_derivative_compose p q x

theorem contract_JL099_definition (a : Nat) (p : Polynomial) : derivative (a::p) = add p (0::derivative p) := rfl

theorem contract_JL099_boundary1 : evaluate (derivative (compose [0,0,1] [1,1])) 2 = 6 := by decide

theorem contract_JL099_boundary2 : evaluate (derivative (multiply [] [1,1])) 3 = 0 := by decide

#print axioms JonnyLean.Polynomials.evaluate_derivative_compose
#print axioms contract_JL099
