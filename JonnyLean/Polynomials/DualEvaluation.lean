import JonnyLean.Polynomials.DerivativeRules

namespace JonnyLean.Polynomials

/-- Horner evaluator computing value and formal derivative in one traversal. -/
def evaluateDual : Polynomial → Nat → Nat × Nat
  | [], _ => (0,0)
  | a::p, x =>
    let z := evaluateDual p x
    (a+x*z.1, z.1+x*z.2)

theorem evaluateDual_correct (p : Polynomial) (x : Nat) :
    evaluateDual p x = (evaluate p x, evaluate (derivative p) x) := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [evaluateDual, ih, evaluate, evaluate_derivative_cons]

theorem evaluateDual_value (p : Polynomial) (x : Nat) :
    (evaluateDual p x).1 = evaluate p x := by rw [evaluateDual_correct]

theorem evaluateDual_derivative (p : Polynomial) (x : Nat) :
    (evaluateDual p x).2 = evaluate (derivative p) x := by rw [evaluateDual_correct]

theorem evaluateDual_product (p q : Polynomial) (x : Nat) :
    evaluateDual (multiply p q) x =
      ((evaluateDual p x).1*(evaluateDual q x).1,
       (evaluateDual p x).2*(evaluateDual q x).1+(evaluateDual p x).1*(evaluateDual q x).2) := by
  simp [evaluateDual_correct, evaluate_multiply, evaluate_derivative_multiply]

theorem evaluateDual_chain (p q : Polynomial) (x : Nat) :
    evaluateDual (compose p q) x =
      ((evaluateDual p (evaluate q x)).1,
       (evaluateDual p (evaluate q x)).2*(evaluateDual q x).2) := by
  simp [evaluateDual_correct, evaluate_compose, evaluate_derivative_compose]

end JonnyLean.Polynomials
