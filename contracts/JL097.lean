import JonnyLean.Polynomials.Truncation

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL097 (p : Polynomial) (n x : Nat) :
    evaluate p x = evaluate (p.take n) x + x^n * evaluate (p.drop n) x :=
  evaluate_truncate p n x

theorem contract_JL097_definition (p : Polynomial) (n : Nat) : p.take n ++ p.drop n = p := List.take_append_drop n p

theorem contract_JL097_boundary1 : evaluate ([3,2,1].take 0) 10 = 0 := by decide

theorem contract_JL097_boundary2 : evaluate [3,2,1] 10 % (10^2) = 23 := by decide

#print axioms JonnyLean.Polynomials.evaluate_truncate
#print axioms contract_JL097
