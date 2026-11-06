import JonnyLean.Polynomials.DualEvaluation

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL100 (p : Polynomial) (x : Nat) :
    evaluateDual p x = (evaluate p x, evaluate (derivative p) x) :=
  evaluateDual_correct p x

theorem contract_JL100_definition (a x : Nat) (p : Polynomial) : evaluateDual (a::p) x = (a+x*(evaluateDual p x).1,(evaluateDual p x).1+x*(evaluateDual p x).2) := rfl

theorem contract_JL100_boundary1 : evaluateDual [] 0 = (0,0) := by decide

theorem contract_JL100_boundary2 : evaluateDual [3,2,1] 4 = (27,10) := by decide

#print axioms JonnyLean.Polynomials.evaluateDual_correct
#print axioms contract_JL100
