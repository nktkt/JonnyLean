import JonnyLean.Arithmetic.RadixResidue

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL073 (m b : Nat) (xs ys : List Nat) :
    radixResidue m b (xs ++ ys) =
      (radixResidue m b xs + b^xs.length * radixResidue m b ys) % m :=
  radixResidue_append m b xs ys

theorem contract_JL073_definition (m b d : Nat) (ds : List Nat) : radixResidue m b (d::ds) = (d+b*radixResidue m b ds)%m := rfl

theorem contract_JL073_boundary1 : radixResidue 0 10 [3,2,1] = 123 := by decide

theorem contract_JL073_boundary2 : radixResidue 7 10 [3,2,1] = 4 := by decide

#print axioms JonnyLean.Arithmetic.radixResidue_append
#print axioms contract_JL073
