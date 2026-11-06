import JonnyLean.Arithmetic.CoprimeCancel

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL069 (a b c : Nat) (h : Nat.gcd a b = 1) :
    a*b ∣ c ↔ a ∣ c ∧ b ∣ c :=
  coprime_product_dvd_iff a b c h

theorem contract_JL069_definition (a b c : Nat) : (a*b ∣ c) ↔ ∃ k, c = a*b*k := Iff.rfl

theorem contract_JL069_boundary1 : (6:Nat)*5 ∣ 90 := by decide

theorem contract_JL069_boundary2 : ¬ ((6:Nat)*4 ∣ 12) := by decide

#print axioms JonnyLean.Arithmetic.coprime_product_dvd_iff
#print axioms contract_JL069
