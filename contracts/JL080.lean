import JonnyLean.Arithmetic.CommonDivisors

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL080 (a : Nat) (xs : List Nat) :
    Nat.gcd (listGcd (a::xs)) (listLcm (a::xs)) = listGcd (a::xs) :=
  listGcd_listLcm_absorb a xs

theorem contract_JL080_definition (a : Nat) (xs : List Nat) : (listGcd (a::xs),listLcm (a::xs),product (a::xs)) = (Nat.gcd a (listGcd xs),Nat.lcm a (listLcm xs),a*product xs) := rfl

theorem contract_JL080_boundary1 : Nat.gcd (listGcd [6,10,15]) (listLcm [6,10,15]) = 1 := by decide

theorem contract_JL080_boundary2 : listLcm [0,6] = 0 := by decide

#print axioms JonnyLean.Arithmetic.listGcd_listLcm_absorb
#print axioms contract_JL080
