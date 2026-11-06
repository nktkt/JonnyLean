import JonnyLean.Polynomials.Composition

namespace JonnyLean.Polynomials

def power (p : Polynomial) : Nat → Polynomial
  | 0 => [1]
  | n+1 => multiply (power p n) p

theorem evaluate_power (p : Polynomial) (n x : Nat) :
    evaluate (power p n) x = (evaluate p x)^n := by
  induction n with
  | zero => simp [power, evaluate]
  | succ n ih => simp [power, evaluate_multiply, ih, Nat.pow_succ]

theorem evaluate_power_add (p : Polynomial) (m n x : Nat) :
    evaluate (power p (m+n)) x = evaluate (multiply (power p m) (power p n)) x := by
  simp only [evaluate_power, evaluate_multiply, Nat.pow_add]

theorem evaluate_power_mul (p : Polynomial) (m n x : Nat) :
    evaluate (power p (m*n)) x = evaluate (power (power p m) n) x := by
  simp only [evaluate_power, Nat.pow_mul]

theorem evaluate_compose_power (p q : Polynomial) (n x : Nat) :
    evaluate (compose (power p n) q) x = evaluate (power (compose p q) n) x := by
  simp only [evaluate_compose, evaluate_power]

end JonnyLean.Polynomials
