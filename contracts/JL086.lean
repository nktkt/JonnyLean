import JonnyLean.Polynomials.Composition

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL086 (p q : Polynomial) (x : Nat) :
    evaluate (compose p q) x = evaluate p (evaluate q x) :=
  evaluate_compose p q x

theorem contract_JL086_definition (a : Nat) (p q : Polynomial) : compose (a::p) q = add [a] (multiply q (compose p q)) := rfl

theorem contract_JL086_boundary1 : evaluate (compose [] [1,1]) 5 = 0 := by decide

theorem contract_JL086_boundary2 : evaluate (compose [1,0,1] [1,1]) 2 = 10 := by decide

#print axioms JonnyLean.Polynomials.evaluate_compose
#print axioms contract_JL086
