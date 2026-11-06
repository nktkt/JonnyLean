import JonnyLean.Polynomials.Evaluation

namespace JonnyLean.Polynomials

theorem evaluate_mono (p : Polynomial) (x y : Nat) (h : x ≤ y) : evaluate p x ≤ evaluate p y := by
  induction p with
  | nil => exact Nat.le_refl 0
  | cons a p ih => exact Nat.add_le_add_left (Nat.mul_le_mul h ih) a

def CoefficientLE : Polynomial → Polynomial → Prop
  | [], _ => True
  | _::_, [] => False
  | a::p, b::q => a ≤ b ∧ CoefficientLE p q

theorem evaluate_coefficients_mono (p q : Polynomial) (x : Nat)
    (h : CoefficientLE p q) : evaluate p x ≤ evaluate q x := by
  induction p generalizing q with
  | nil => exact Nat.zero_le _
  | cons a p ih =>
    cases q with
    | nil => exact False.elim h
    | cons b q => exact Nat.add_le_add h.1 (Nat.mul_le_mul_left x (ih q h.2))

theorem evaluate_constant_lower (a : Nat) (p : Polynomial) (x : Nat) :
    a ≤ evaluate (a::p) x := Nat.le_add_right a _

theorem evaluate_prefix_lower (p q : Polynomial) (x : Nat) :
    evaluate p x ≤ evaluate (p++q) x := by
  rw [evaluate_append]
  exact Nat.le_add_right _ _

theorem evaluate_positive_of_constant (a : Nat) (p : Polynomial) (x : Nat) (ha : 0 < a) :
    0 < evaluate (a::p) x := Nat.lt_of_lt_of_le ha (evaluate_constant_lower a p x)

end JonnyLean.Polynomials
