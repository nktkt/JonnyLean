import JonnyLean.NumberTheory.Triangular

namespace JL003Contract

/-- The intended summation is defined independently of the implementation. -/
def expectedSum : Nat → Nat
  | 0 => 0
  | n + 1 => expectedSum n + (n + 1)

-- Direct assignment checks all arguments and the conclusion of the named theorem.
theorem namedTarget : ∀ n : Nat, 2 * JonnyLean.triangular n = n * (n + 1) :=
  JonnyLean.triangular_formula

theorem sum_agrees (n : Nat) : JonnyLean.triangular n = expectedSum n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change JonnyLean.triangular n + (n + 1) = expectedSum n + (n + 1)
    rw [ih]

/-- The formula is also checked with an independent definition of the sum. -/
theorem target (n : Nat) : 2 * expectedSum n = n * (n + 1) := by
  rw [← sum_agrees n]
  exact namedTarget n

-- These are definitional checks, not consequences of the formula alone.
example : JonnyLean.triangular 0 = 0 := rfl
example (n : Nat) :
    JonnyLean.triangular (n + 1) = JonnyLean.triangular n + (n + 1) := rfl

example : JonnyLean.triangular 1 = 1 := rfl
example : JonnyLean.triangular 2 = 3 := rfl
example : JonnyLean.triangular 5 = 15 := rfl
example : 2 * expectedSum 0 = 0 * (0 + 1) := target 0
example : 2 * expectedSum 1 = 1 * (1 + 1) := target 1
example : 2 * expectedSum 5 = 5 * (5 + 1) := target 5

end JL003Contract

#print axioms JonnyLean.triangular_formula
#print axioms JL003Contract.target
