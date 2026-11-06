import JonnyLean.Polynomials.Derivative

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL098 (p q : Polynomial) (x : Nat) :
    evaluate (derivative (add p q)) x =
      evaluate (derivative p) x + evaluate (derivative q) x :=
  evaluate_derivative_add p q x

theorem contract_JL098_definition (a : Nat) (p : Polynomial) : derivative (a::p) = add p (0::derivative p) := rfl

theorem contract_JL098_boundary1 : evaluate (derivative [7]) 5 = 0 := by decide

theorem contract_JL098_boundary2 : evaluate (derivative [3,2,1]) 4 = 10 := by decide

#print axioms JonnyLean.Polynomials.evaluate_derivative_add
#print axioms contract_JL098
