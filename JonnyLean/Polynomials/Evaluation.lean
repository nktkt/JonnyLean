import Std

namespace JonnyLean.Polynomials

abbrev Polynomial := List Nat

/-- Coefficients are in ascending order; no trailing-zero normalization is imposed. -/
def evaluate : Polynomial → Nat → Nat
  | [], _ => 0
  | a :: p, x => a + x * evaluate p x

theorem evaluate_append (p q : Polynomial) (x : Nat) :
    evaluate (p++q) x = evaluate p x + x^p.length * evaluate q x := by
  induction p with
  | nil => simp [evaluate]
  | cons a p ih =>
    simp only [List.cons_append, evaluate, ih, List.length_cons, Nat.pow_succ,
      Nat.mul_add, Nat.mul_assoc]
    ac_rfl

theorem evaluate_zero (a : Nat) (p : Polynomial) : evaluate (a::p) 0 = a := by
  simp [evaluate]

theorem evaluate_singleton (a x : Nat) : evaluate [a] x = a := by simp [evaluate]

theorem evaluate_append_zero (p : Polynomial) (x : Nat) : evaluate (p++[0]) x = evaluate p x := by
  simp [evaluate_append, evaluate]

theorem evaluate_replicate_zero (n x : Nat) : evaluate (List.replicate n 0) x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, evaluate, ih]

end JonnyLean.Polynomials
