import JonnyLean.Polynomials.Multiplication

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL085 (p q : Polynomial) (x : Nat) :
    evaluate (multiply p q) x = evaluate p x * evaluate q x :=
  evaluate_multiply p q x

theorem contract_JL085_definition (a : Nat) (p q : Polynomial) : multiply (a::p) q = add (scale a q) (0::multiply p q) := rfl

theorem contract_JL085_boundary1 : evaluate (multiply [] [2,3]) 9 = 0 := by decide

theorem contract_JL085_boundary2 : evaluate (multiply [1,1] [1,1]) 3 = 16 := by decide

#print axioms JonnyLean.Polynomials.evaluate_multiply
#print axioms contract_JL085
