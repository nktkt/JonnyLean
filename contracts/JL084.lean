import JonnyLean.Polynomials.Shift

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL084 (n : Nat) (p : Polynomial) (x : Nat) :
    evaluate (shift n p) x = x^n * evaluate p x :=
  evaluate_shift n p x

theorem contract_JL084_definition (n : Nat) (p : Polynomial) : shift (n+1) p = 0::shift n p := rfl

theorem contract_JL084_boundary1 : shift 0 [] = [] := by decide

theorem contract_JL084_boundary2 : evaluate (shift 2 [3,1]) 4 = 112 := by decide

#print axioms JonnyLean.Polynomials.evaluate_shift
#print axioms contract_JL084
