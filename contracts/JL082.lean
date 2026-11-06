import JonnyLean.Polynomials.Addition

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL082 (p q : Polynomial) (x : Nat) :
    evaluate (add p q) x = evaluate p x + evaluate q x :=
  evaluate_add p q x

theorem contract_JL082_definition (a b : Nat) (p q : Polynomial) : add (a::p) (b::q) = (a+b)::add p q := rfl

theorem contract_JL082_boundary1 : add [] [1,2] = [1,2] := by decide

theorem contract_JL082_boundary2 : add [1,2] [3] = [4,2] := by decide

#print axioms JonnyLean.Polynomials.evaluate_add
#print axioms contract_JL082
