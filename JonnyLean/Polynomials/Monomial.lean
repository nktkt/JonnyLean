import JonnyLean.Polynomials.Equivalence

namespace JonnyLean.Polynomials

def monomial (a n : Nat) : Polynomial := shift n [a]

theorem evaluate_monomial (a n x : Nat) : evaluate (monomial a n) x = a*x^n := by
  simp [monomial, evaluate_shift, evaluate, Nat.mul_comm]

theorem monomial_length (a n : Nat) : (monomial a n).length = n+1 := by
  simp [monomial, shift_length]

theorem monomial_multiply (a b m n : Nat) :
    Equivalent (multiply (monomial a m) (monomial b n)) (monomial (a*b) (m+n)) := by
  intro x
  simp only [evaluate_multiply, evaluate_monomial, Nat.pow_add]
  ac_rfl

theorem monomial_add (a b n : Nat) :
    Equivalent (add (monomial a n) (monomial b n)) (monomial (a+b) n) := by
  intro x
  simp only [evaluate_add, evaluate_monomial, Nat.add_mul]

theorem monomial_compose (a b m n : Nat) :
    Equivalent (compose (monomial a m) (monomial b n)) (monomial (a*b^m) (n*m)) := by
  intro x
  simp only [evaluate_compose, evaluate_monomial, Nat.mul_pow, Nat.pow_mul, Nat.mul_assoc]

end JonnyLean.Polynomials
