import JonnyLean.Arithmetic.GcdTriple

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL061 (d a b c : Nat) :
    d ∣ gcdTriple a b c ↔ d ∣ a ∧ d ∣ b ∧ d ∣ c :=
  dvd_gcdTriple d a b c

theorem contract_JL061_definition (a b c : Nat) : gcdTriple a b c = Nat.gcd a (Nat.gcd b c) := rfl

theorem contract_JL061_boundary1 : gcdTriple 0 0 0 = 0 := by decide

theorem contract_JL061_boundary2 : gcdTriple 18 30 42 = 6 := by decide

#print axioms JonnyLean.Arithmetic.dvd_gcdTriple
#print axioms contract_JL061
