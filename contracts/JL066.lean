import JonnyLean.Arithmetic.LcmList

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL066 (xs : List Nat) (d : Nat) :
    listLcm xs ∣ d ↔ ∀ a ∈ xs, a ∣ d :=
  listLcm_dvd xs d

theorem contract_JL066_definition (a : Nat) (xs : List Nat) : listLcm (a::xs) = Nat.lcm a (listLcm xs) := rfl

theorem contract_JL066_boundary1 : listLcm [] = 1 := by decide

theorem contract_JL066_boundary2 : listLcm [6,10,15] = 30 := by decide

#print axioms JonnyLean.Arithmetic.listLcm_dvd
#print axioms contract_JL066
