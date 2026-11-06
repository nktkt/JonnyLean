import JonnyLean.Polynomials.Multiplication

namespace JonnyLean.Polynomials

def compose : Polynomial → Polynomial → Polynomial
  | [], _ => []
  | a::p, q => add [a] (multiply q (compose p q))

theorem evaluate_compose (p q : Polynomial) (x : Nat) :
    evaluate (compose p q) x = evaluate p (evaluate q x) := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [compose, evaluate_add, evaluate_multiply, evaluate, ih]

theorem evaluate_compose_assoc (p q r : Polynomial) (x : Nat) :
    evaluate (compose (compose p q) r) x = evaluate (compose p (compose q r)) x := by
  simp only [evaluate_compose]

theorem evaluate_compose_identity (p : Polynomial) (x : Nat) :
    evaluate (compose p [0,1]) x = evaluate p x := by simp [evaluate_compose, evaluate]

theorem evaluate_compose_constant (p : Polynomial) (c x : Nat) :
    evaluate (compose p [c]) x = evaluate p c := by simp [evaluate_compose, evaluate]

theorem evaluate_compose_add (p q r : Polynomial) (x : Nat) :
    evaluate (compose (add p q) r) x = evaluate (add (compose p r) (compose q r)) x := by
  simp only [evaluate_compose, evaluate_add]

end JonnyLean.Polynomials
