import JonnyLean.Polynomials.Scalar

namespace JonnyLean.Polynomials

/-- Formal derivative by the recurrence D(a+X p)=p+X Dp. -/
def derivative : Polynomial → Polynomial
  | [] => []
  | _::p => add p (0 :: derivative p)

theorem evaluate_derivative_cons (a : Nat) (p : Polynomial) (x : Nat) :
    evaluate (derivative (a::p)) x = evaluate p x + x*evaluate (derivative p) x := by
  simp [derivative, evaluate_add, evaluate]

theorem evaluate_derivative_add (p q : Polynomial) (x : Nat) :
    evaluate (derivative (add p q)) x =
      evaluate (derivative p) x + evaluate (derivative q) x := by
  induction p generalizing q with
  | nil => simp [add, derivative, evaluate]
  | cons a p ih =>
    cases q with
    | nil => simp [add, derivative, evaluate]
    | cons b q =>
      simp only [add, evaluate_derivative_cons, evaluate_add, ih, Nat.mul_add]
      ac_rfl

theorem evaluate_derivative_scale (c : Nat) (p : Polynomial) (x : Nat) :
    evaluate (derivative (scale c p)) x = c*evaluate (derivative p) x := by
  induction p with
  | nil => simp [scale, derivative, evaluate]
  | cons a p ih =>
    change evaluate (derivative ((c*a)::scale c p)) x = c*evaluate (derivative (a::p)) x
    simp only [evaluate_derivative_cons, evaluate_scale, ih, Nat.mul_add]
    ac_rfl

theorem evaluate_derivative_constant (c x : Nat) : evaluate (derivative [c]) x = 0 := by
  simp [derivative, add, evaluate]

theorem evaluate_derivative_affine (a b x : Nat) : evaluate (derivative [a,b]) x = b := by
  simp [derivative, add, evaluate]

end JonnyLean.Polynomials
