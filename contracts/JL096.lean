import JonnyLean.Polynomials.Monotonicity

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL096 (p q : Polynomial) (x : Nat)
    (h : CoefficientLE p q) : evaluate p x ≤ evaluate q x :=
  evaluate_coefficients_mono p q x h

theorem contract_JL096_definition (a b : Nat) (p q : Polynomial) : CoefficientLE (a::p) (b::q) ↔ a ≤ b ∧ CoefficientLE p q := Iff.rfl

theorem contract_JL096_boundary1 : evaluate [1,2] 3 ≤ evaluate [2,3,4] 3 := by decide

theorem contract_JL096_boundary2 : evaluate [0,0,1] 0 = 0 := by decide

#print axioms JonnyLean.Polynomials.evaluate_coefficients_mono
#print axioms contract_JL096
