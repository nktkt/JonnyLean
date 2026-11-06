import JonnyLean.Arithmetic.EuclidAvoidance

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL079 (xs : List Nat) (k a : Nat) (ha : a ∈ xs) (h : 1 < a) :
    ¬ a ∣ avoidance xs k :=
  avoidance_not_dvd xs k a ha h

theorem contract_JL079_definition (xs : List Nat) (k : Nat) : avoidance xs k = product xs*k+1 := rfl

theorem contract_JL079_boundary1 : avoidance [] 0 = 1 := by decide

theorem contract_JL079_boundary2 : avoidance [2,3,5] 1 = 31 := by decide

#print axioms JonnyLean.Arithmetic.avoidance_not_dvd
#print axioms contract_JL079
