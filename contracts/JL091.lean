import JonnyLean.Polynomials.FiniteSum

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL091 (ps : List Polynomial) (x : Nat) :
    evaluate (sumPolynomials ps) x = Arithmetic.weightedSum (fun p => evaluate p x) ps :=
  evaluate_sumPolynomials ps x

theorem contract_JL091_definition (p : Polynomial) (ps : List Polynomial) : sumPolynomials (p::ps) = add p (sumPolynomials ps) := rfl

theorem contract_JL091_boundary1 : sumPolynomials [] = [] := by decide

theorem contract_JL091_boundary2 : evaluate (sumPolynomials [[1,2],[3],[0,1]]) 4 = 16 := by decide

#print axioms JonnyLean.Polynomials.evaluate_sumPolynomials
#print axioms contract_JL091
