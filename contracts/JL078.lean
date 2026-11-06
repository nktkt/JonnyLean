import JonnyLean.Arithmetic.RangeProduct

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL078 (f : Nat → Nat) (m n : Nat) :
    rangeProduct f (m+n) = rangeProduct f m * rangeProduct (fun i => f (m+i)) n :=
  rangeProduct_split f m n

theorem contract_JL078_definition (f : Nat → Nat) (n : Nat) : rangeProduct f (n+1) = rangeProduct f n*f n := rfl

theorem contract_JL078_boundary1 : rangeProduct (fun n => n+1) 0 = 1 := by decide

theorem contract_JL078_boundary2 : rangeProduct (fun n => n+1) 5 = 120 := by decide

#print axioms JonnyLean.Arithmetic.rangeProduct_split
#print axioms contract_JL078
