import JonnyLean.NumberTheory.FactorialDivisibility

/- Independent, named contract for JL-021. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL021

def factorialSpec : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorialSpec n

theorem factorial_matches (n : Nat) : factorialSpec n = JonnyLean.factorial n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [factorialSpec, JonnyLean.factorial, ih]

/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ k n : Nat, 0 < k → k ≤ n → ∃ w : Nat, factorialSpec n = k * w :=
  by
  intro k n hk hkn
  simpa only [factorial_matches, JonnyLean.Divides] using JonnyLean.positive_le_divides_factorial k n hk hkn

theorem smallest_factor : ∃ w : Nat, factorialSpec 1 = 1 * w := ⟨1, rfl⟩

theorem interior_factor : ∃ w : Nat, factorialSpec 5 = 3 * w := ⟨40, rfl⟩

theorem zero_excluded : ¬ (∃ w : Nat, factorialSpec 0 = 0 * w) := by simp [factorialSpec]

end JonnyLean.Contracts.JL021

#print axioms JonnyLean.positive_le_divides_factorial
#print axioms JonnyLean.Contracts.JL021.contract
