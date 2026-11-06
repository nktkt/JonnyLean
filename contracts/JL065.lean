import JonnyLean.Arithmetic.LcmTriple

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL065 (a b c d : Nat) :
    lcmTriple a b c ∣ d ↔ a ∣ d ∧ b ∣ d ∧ c ∣ d :=
  lcmTriple_dvd a b c d

theorem contract_JL065_definition (a b c : Nat) : lcmTriple a b c = Nat.lcm a (Nat.lcm b c) := rfl

theorem contract_JL065_boundary1 : lcmTriple 0 6 10 = 0 := by decide

theorem contract_JL065_boundary2 : lcmTriple 6 10 15 = 30 := by decide

#print axioms JonnyLean.Arithmetic.lcmTriple_dvd
#print axioms contract_JL065
