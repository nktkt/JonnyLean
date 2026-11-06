import JonnyLean.Polynomials.Dilation

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL094 (c : Nat) (p : Polynomial) (x : Nat) :
    evaluate (dilate c p) x = evaluate p (c*x) :=
  evaluate_dilate c p x

theorem contract_JL094_definition (c a : Nat) (p : Polynomial) : dilate c (a::p) = a::scale c (dilate c p) := rfl

theorem contract_JL094_boundary1 : dilate 0 [3,2,1] = [3,0,0] := by decide

theorem contract_JL094_boundary2 : dilate 2 [3,2,1] = [3,4,4] := by decide

#print axioms JonnyLean.Polynomials.evaluate_dilate
#print axioms contract_JL094
