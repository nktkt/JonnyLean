import JonnyLean.Polynomials.Shift

namespace JonnyLean.Polynomials

def multiply : Polynomial → Polynomial → Polynomial
  | [], _ => []
  | a::p, q => add (scale a q) (0 :: multiply p q)

theorem evaluate_multiply (p q : Polynomial) (x : Nat) :
    evaluate (multiply p q) x = evaluate p x * evaluate q x := by
  induction p with
  | nil => simp [multiply, evaluate]
  | cons a p ih =>
    simp only [multiply, evaluate_add, evaluate_scale, evaluate, Nat.zero_add, ih, Nat.add_mul]
    rw [Nat.mul_assoc]

theorem evaluate_multiply_comm (p q : Polynomial) (x : Nat) :
    evaluate (multiply p q) x = evaluate (multiply q p) x := by
  simp only [evaluate_multiply, Nat.mul_comm]

theorem evaluate_multiply_assoc (p q r : Polynomial) (x : Nat) :
    evaluate (multiply (multiply p q) r) x = evaluate (multiply p (multiply q r)) x := by
  simp only [evaluate_multiply, Nat.mul_assoc]

theorem evaluate_multiply_add (p q r : Polynomial) (x : Nat) :
    evaluate (multiply p (add q r)) x = evaluate (add (multiply p q) (multiply p r)) x := by
  simp only [evaluate_multiply, evaluate_add, Nat.mul_add]

theorem evaluate_multiply_one (p : Polynomial) (x : Nat) :
    evaluate (multiply p [1]) x = evaluate p x := by simp [evaluate_multiply, evaluate]

end JonnyLean.Polynomials
