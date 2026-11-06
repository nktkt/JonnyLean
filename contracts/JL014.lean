import JonnyLean.Algebra.Quadratic

/- Independent, named contract for JL-014. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL014


/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ a b : Nat, (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
  JonnyLean.square_add

theorem zero_pair : (0 + 0 : Nat) ^ 2 = 0 ^ 2 + 2 * 0 * 0 + 0 ^ 2 := rfl

theorem square_five : (2 + 3 : Nat) ^ 2 = 2 ^ 2 + 2 * 2 * 3 + 3 ^ 2 := rfl

end JonnyLean.Contracts.JL014

#print axioms JonnyLean.square_add
#print axioms JonnyLean.Contracts.JL014.contract
