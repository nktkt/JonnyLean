import JonnyLean.Arithmetic.EuclidTrace

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL064 (a b : Nat) :
    euclidRun (a+1) (a,b) = (0, Nat.gcd a b) :=
  euclidRun_computes a b

theorem contract_JL064_definition (a b : Nat) : euclidStep (a,b) = (if a = 0 then (a,b) else (b%a,a)) := rfl

theorem contract_JL064_boundary1 : euclidRun 1 (0,0) = (0,0) := by decide

theorem contract_JL064_boundary2 : euclidRun 5 (48,18) = (0,6) := by decide

#print axioms JonnyLean.Arithmetic.euclidRun_computes
#print axioms contract_JL064
