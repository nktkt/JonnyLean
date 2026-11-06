import JonnyLean.NumberTheory.Factorial

/- Independent, named contract for JL-020. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL020

def factorialSpec : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorialSpec n

theorem factorial_matches (n : Nat) : factorialSpec n = JonnyLean.factorial n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [factorialSpec, JonnyLean.factorial, ih]

/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ m n : Nat, m ≤ n → factorialSpec m ≤ factorialSpec n :=
  by
  intro m n h
  simpa only [factorial_matches] using JonnyLean.factorial_mono m n h

theorem empty_product : factorialSpec 0 = 1 := rfl

theorem equal_first_values : factorialSpec 0 = factorialSpec 1 := rfl

theorem factorial_five : factorialSpec 5 = 120 := rfl

end JonnyLean.Contracts.JL020

#print axioms JonnyLean.factorial_mono
#print axioms JonnyLean.Contracts.JL020.contract
