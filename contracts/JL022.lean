import JonnyLean.NumberTheory.Fibonacci

/- Independent, named contract for JL-022. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL022

def sumSpec (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumSpec f n + f n

theorem sum_matches (f : Nat → Nat) (n : Nat) : sumSpec f n = JonnyLean.rangeSum f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumSpec, JonnyLean.rangeSum, ih]

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
    ∀ n : Nat, sumSpec (fun i => fibonacciSpec (i + 1)) n + 1 = fibonacciSpec (n + 2) :=
  by
  intro n
  simpa only [sum_matches, fibonacci_matches] using JonnyLean.fibonacci_prefix_sum n

theorem initial_values : fibonacciSpec 0 = 0 ∧ fibonacciSpec 1 = 1 := ⟨rfl, rfl⟩

theorem empty_fibonacci_sum : sumSpec (fun i => fibonacciSpec (i + 1)) 0 + 1 = fibonacciSpec 2 := rfl

theorem first_five_sum : sumSpec (fun i => fibonacciSpec (i + 1)) 5 + 1 = 13 := rfl

end JonnyLean.Contracts.JL022

#print axioms JonnyLean.fibonacci_prefix_sum
#print axioms JonnyLean.Contracts.JL022.contract
