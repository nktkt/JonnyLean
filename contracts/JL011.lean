import JonnyLean.NumberTheory.Congruence

/- Independent, named contract for JL-011. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL011


/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ m a r : Nat, r < m → a % m = r % m → r = a % m :=
  JonnyLean.congruent_unique_remainder

theorem zero_value : (0 : Nat) = 0 % 5 := rfl

theorem remainder_two : (2 : Nat) = 17 % 5 := rfl

theorem modulus_zero : ∀ a b : Nat, a % 0 = b % 0 ↔ a = b := by simp

end JonnyLean.Contracts.JL011

#print axioms JonnyLean.congruent_unique_remainder
#print axioms JonnyLean.Contracts.JL011.contract
