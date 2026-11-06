import JonnyLean.Polynomials.Equivalence

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL088 (p q r s : Polynomial) (h : Equivalent p q) (k : Equivalent r s) :
    Equivalent (compose p r) (compose q s) :=
  equivalent_compose p q r s h k

theorem contract_JL088_definition (p q : Polynomial) : Equivalent p q ↔ ∀ x, evaluate p x = evaluate q x := Iff.rfl

theorem contract_JL088_boundary1 : evaluate ([] : Polynomial) 7 = evaluate [0] 7 := by decide

theorem contract_JL088_boundary2 : evaluate [1,2] 3 = evaluate [1,2,0] 3 := by decide

#print axioms JonnyLean.Polynomials.equivalent_compose
#print axioms contract_JL088
