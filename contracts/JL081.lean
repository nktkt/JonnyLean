import JonnyLean.Polynomials.Evaluation

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL081 (p q : Polynomial) (x : Nat) :
    evaluate (p++q) x = evaluate p x + x^p.length * evaluate q x :=
  evaluate_append p q x

theorem contract_JL081_definition (a x : Nat) (p : Polynomial) : evaluate (a::p) x = a+x*evaluate p x := rfl

theorem contract_JL081_boundary1 : evaluate [] 0 = 0 := by decide

theorem contract_JL081_boundary2 : evaluate [3,2,1] 10 = 123 := by decide

#print axioms JonnyLean.Polynomials.evaluate_append
#print axioms contract_JL081
