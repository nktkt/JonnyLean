import JonnyLean.Polynomials.Scalar

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL083 (c : Nat) (p : Polynomial) (x : Nat) :
    evaluate (scale c p) x = c*evaluate p x :=
  evaluate_scale c p x

theorem contract_JL083_definition (c : Nat) (p : Polynomial) : scale c p = p.map (fun a => c*a) := rfl

theorem contract_JL083_boundary1 : scale 0 [3,2,1] = [0,0,0] := by decide

theorem contract_JL083_boundary2 : evaluate (scale 7 [3,2]) 5 = 91 := by decide

#print axioms JonnyLean.Polynomials.evaluate_scale
#print axioms contract_JL083
