import JonnyLean.Arithmetic.WeightedResidue

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL074 (m : Nat) (w v : α → Nat) (xs : List α)
    (h : ∀ a ∈ xs, w a % m = v a % m) :
    weightedSum w xs % m = weightedSum v xs % m :=
  weightedSum_residue m w v xs h

theorem contract_JL074_definition (w : α → Nat) (a : α) (xs : List α) : weightedSum w (a::xs) = w a+weightedSum w xs := rfl

theorem contract_JL074_boundary1 : weightedSum (fun n : Nat => n*n) [] = 0 := by decide

theorem contract_JL074_boundary2 : weightedSum (fun n : Nat => n*n) [1,2,3] = 14 := by decide

#print axioms JonnyLean.Arithmetic.weightedSum_residue
#print axioms contract_JL074
