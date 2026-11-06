import JonnyLean.Arithmetic.ReducedPair

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL070 (a b : Nat) (h : 0 < a ∨ 0 < b) :
    Nat.gcd (reducedPair a b).1 (reducedPair a b).2 = 1 :=
  reducedPair_coprime a b h

theorem contract_JL070_definition (a b : Nat) : reducedPair a b = (a/Nat.gcd a b,b/Nat.gcd a b) := rfl

theorem contract_JL070_boundary1 : reducedPair 0 0 = (0,0) := by decide

theorem contract_JL070_boundary2 : reducedPair 18 30 = (3,5) := by decide

#print axioms JonnyLean.Arithmetic.reducedPair_coprime
#print axioms contract_JL070
