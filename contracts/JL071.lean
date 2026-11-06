import JonnyLean.Arithmetic.PrimitiveScale

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL071 (a b c d k l : Nat)
    (hab : Nat.gcd a b = 1) (hcd : Nat.gcd c d = 1)
    (h₁ : k*a = l*c) (h₂ : k*b = l*d) : k = l :=
  primitive_scale_unique a b c d k l hab hcd h₁ h₂

theorem contract_JL071_definition (a b k : Nat) : reducedPair (k*a) (k*b) = ((k*a)/Nat.gcd (k*a) (k*b),(k*b)/Nat.gcd (k*a) (k*b)) := rfl

theorem contract_JL071_boundary1 : reducedPair (0*3) (0*5) = (0,0) := by decide

theorem contract_JL071_boundary2 : Nat.gcd (7*3) (7*5) = 7 := by decide

#print axioms JonnyLean.Arithmetic.primitive_scale_unique
#print axioms contract_JL071
