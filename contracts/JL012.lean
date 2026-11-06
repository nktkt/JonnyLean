import JonnyLean.NumberTheory.CongruenceOperations

/- Independent, named contract for JL-012. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL012


/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ m a b u v w : Nat, a % m = b % m → (u * a ^ 2 + v * a + w) % m = (u * b ^ 2 + v * b + w) % m :=
  JonnyLean.congruent_quadratic

theorem modulus_one : (7 * 3 ^ 2 + 2 * 3 + 9) % 1 = (7 * 8 ^ 2 + 2 * 8 + 9) % 1 := rfl

theorem quadratic_example : (2 * 3 ^ 2 + 3 + 4) % 5 = (2 * 8 ^ 2 + 8 + 4) % 5 := rfl

theorem zero_modulus : (2 * 3 ^ 2 + 3 + 4) % 0 = (2 * 3 ^ 2 + 3 + 4) % 0 := rfl

end JonnyLean.Contracts.JL012

#print axioms JonnyLean.congruent_quadratic
#print axioms JonnyLean.Contracts.JL012.contract
