import JonnyLean.Arithmetic.Shear

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL063 (ks : List Nat) (s : Nat × Nat) (d : Nat) :
    (d ∣ (shearTrace ks s).1 ∧ d ∣ (shearTrace ks s).2) ↔
    (d ∣ s.1 ∧ d ∣ s.2) :=
  shearTrace_common ks s d

theorem contract_JL063_definition (k a b : Nat) : shear k (a,b) = (b,a+k*b) := rfl

theorem contract_JL063_boundary1 : shearTrace [] (0,0) = (0,0) := by decide

theorem contract_JL063_boundary2 : shearTrace [2,3] (6,9) = (24,81) := by decide

#print axioms JonnyLean.Arithmetic.shearTrace_common
#print axioms contract_JL063
