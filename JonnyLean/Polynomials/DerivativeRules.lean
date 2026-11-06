import JonnyLean.Polynomials.Derivative
import JonnyLean.Polynomials.Translation

namespace JonnyLean.Polynomials

theorem evaluate_derivative_multiply (p q : Polynomial) (x : Nat) :
    evaluate (derivative (multiply p q)) x =
      evaluate (derivative p) x * evaluate q x + evaluate p x * evaluate (derivative q) x := by
  induction p with
  | nil => simp [multiply, derivative, evaluate]
  | cons a p ih =>
    rw [multiply, evaluate_derivative_add, evaluate_derivative_scale]
    simp only [evaluate_derivative_cons, evaluate_multiply, ih, evaluate, Nat.mul_add, Nat.add_mul]
    ac_rfl

theorem evaluate_derivative_compose (p q : Polynomial) (x : Nat) :
    evaluate (derivative (compose p q)) x =
      evaluate (derivative p) (evaluate q x) * evaluate (derivative q) x := by
  induction p with
  | nil => simp [compose, derivative, evaluate]
  | cons a p ih =>
    rw [compose, evaluate_derivative_add, evaluate_derivative_constant, Nat.zero_add,
      evaluate_derivative_multiply]
    simp only [evaluate_compose, ih, evaluate_derivative_cons, Nat.add_mul]
    ac_rfl

theorem evaluate_derivative_square (p : Polynomial) (x : Nat) :
    evaluate (derivative (multiply p p)) x = 2*evaluate p x*evaluate (derivative p) x := by
  rw [evaluate_derivative_multiply]
  simp only [Nat.mul_comm, Nat.mul_assoc]
  omega

theorem evaluate_derivative_translate (c : Nat) (p : Polynomial) (x : Nat) :
    evaluate (derivative (translate c p)) x = evaluate (derivative p) (x+c) := by
  simp [translate, evaluate_derivative_compose, evaluate_derivative_affine, evaluate, Nat.add_comm]

end JonnyLean.Polynomials
