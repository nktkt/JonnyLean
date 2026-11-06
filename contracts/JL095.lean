import JonnyLean.Polynomials.SyntheticDivision

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL095 (a x : Nat) (p : Polynomial) (h : a ≤ x) :
    evaluate p x = evaluate p a + (x-a)*evaluate (dividedDifference a p) x :=
  dividedDifference_remainder a x p h

theorem contract_JL095_definition (a c : Nat) (p : Polynomial) : dividedDifference a (c::p) = add [evaluate p a] (0::dividedDifference a p) := rfl

theorem contract_JL095_boundary1 : evaluate (dividedDifference 7 [5]) 9 = 0 := by decide

theorem contract_JL095_boundary2 : evaluate (dividedDifference 2 [1,0,1]) 5 = 7 := by decide

#print axioms JonnyLean.Polynomials.dividedDifference_remainder
#print axioms contract_JL095
