import JonnyLean.Polynomials.Power
import JonnyLean.Polynomials.Equivalence
import JonnyLean.Arithmetic.Product

namespace JonnyLean.Polynomials

def productPolynomials : List Polynomial → Polynomial
  | [] => [1]
  | p::ps => multiply p (productPolynomials ps)

theorem evaluate_productPolynomials (ps : List Polynomial) (x : Nat) :
    evaluate (productPolynomials ps) x = Arithmetic.product (ps.map (fun p => evaluate p x)) := by
  induction ps with
  | nil => simp [productPolynomials, evaluate, Arithmetic.product]
  | cons p ps ih => simp [productPolynomials, evaluate_multiply, Arithmetic.product, ih]

theorem productPolynomials_append (ps qs : List Polynomial) :
    Equivalent (productPolynomials (ps++qs)) (multiply (productPolynomials ps) (productPolynomials qs)) := by
  intro x
  simp [evaluate_productPolynomials, evaluate_multiply, Arithmetic.product_append]

theorem productPolynomials_replicate (p : Polynomial) (n : Nat) :
    Equivalent (productPolynomials (List.replicate n p)) (power p n) := by
  intro x
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, productPolynomials, evaluate_multiply, evaluate_power] at ih ⊢
    rw [ih, Nat.pow_succ, Nat.mul_comm]

theorem productPolynomials_zero (ps : List Polynomial) (x : Nat) :
    evaluate (productPolynomials ps) x = 0 ↔ ∃ p ∈ ps, evaluate p x = 0 := by
  simp [evaluate_productPolynomials, Arithmetic.product_eq_zero, List.mem_map]

end JonnyLean.Polynomials
