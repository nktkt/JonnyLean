import JonnyLean.Polynomials.FiniteProduct

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL092 (ps : List Polynomial) (x : Nat) :
    evaluate (productPolynomials ps) x = 0 ↔ ∃ p ∈ ps, evaluate p x = 0 :=
  productPolynomials_zero ps x

theorem contract_JL092_definition (p : Polynomial) (ps : List Polynomial) : productPolynomials (p::ps) = multiply p (productPolynomials ps) := rfl

theorem contract_JL092_boundary1 : evaluate (productPolynomials []) 0 = 1 := by decide

theorem contract_JL092_boundary2 : evaluate (productPolynomials [[1,1],[0,1]]) 0 = 0 := by decide

#print axioms JonnyLean.Polynomials.productPolynomials_zero
#print axioms contract_JL092
