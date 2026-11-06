import JonnyLean.NumberTheory.FibonacciAddition

/- Independent, named contract for JL-023. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL023

def fibonacciPairSpec : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => let p := fibonacciPairSpec n; (p.2, p.1 + p.2)

def fibonacciSpec (n : Nat) : Nat := (fibonacciPairSpec n).1

theorem fibonacci_pair_matches (n : Nat) : fibonacciPairSpec n = JonnyLean.fibonacciPair n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [fibonacciPairSpec, JonnyLean.fibonacciPair, ih]

theorem fibonacci_matches (n : Nat) : fibonacciSpec n = JonnyLean.fibonacci n := by
  unfold fibonacciSpec JonnyLean.fibonacci
  rw [fibonacci_pair_matches]

/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ m n : Nat, fibonacciSpec (m + n + 1) = fibonacciSpec (m + 1) * fibonacciSpec (n + 1) + fibonacciSpec m * fibonacciSpec n :=
  by
  intro m n
  simpa only [fibonacci_matches] using JonnyLean.fibonacci_addition m n

theorem zero_indices : fibonacciSpec (0 + 0 + 1) = fibonacciSpec 1 * fibonacciSpec 1 + fibonacciSpec 0 * fibonacciSpec 0 := rfl

theorem addition_example : fibonacciSpec 8 = fibonacciSpec 4 * fibonacciSpec 5 + fibonacciSpec 3 * fibonacciSpec 4 := rfl

theorem double_odd_example : fibonacciSpec 9 = fibonacciSpec 5 ^ 2 + fibonacciSpec 4 ^ 2 := rfl

end JonnyLean.Contracts.JL023

#print axioms JonnyLean.fibonacci_addition
#print axioms JonnyLean.Contracts.JL023.contract
