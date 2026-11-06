import JonnyLean.Polynomials.Monomial

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL090 (a b m n : Nat) :
    Equivalent (compose (monomial a m) (monomial b n)) (monomial (a*b^m) (n*m)) :=
  monomial_compose a b m n

theorem contract_JL090_definition (a n : Nat) : monomial a n = shift n [a] := rfl

theorem contract_JL090_boundary1 : evaluate (monomial 0 0) 0 = 0 := by decide

theorem contract_JL090_boundary2 : evaluate (compose (monomial 2 3) (monomial 5 2)) 2 = 16000 := by decide

#print axioms JonnyLean.Polynomials.monomial_compose
#print axioms contract_JL090
