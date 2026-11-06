import JonnyLean.Polynomials.Scalar

namespace JonnyLean.Polynomials

def shift : Nat → Polynomial → Polynomial
  | 0, p => p
  | n+1, p => 0 :: shift n p

theorem evaluate_shift (n : Nat) (p : Polynomial) (x : Nat) :
    evaluate (shift n p) x = x^n * evaluate p x := by
  induction n with
  | zero => simp [shift]
  | succ n ih => simp [shift, evaluate, ih, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]

theorem shift_add (m n : Nat) (p : Polynomial) : shift (m+n) p = shift m (shift n p) := by
  induction m with
  | zero => simp [shift]
  | succ m ih => simp [Nat.succ_add, shift, ih]

theorem shift_length (n : Nat) (p : Polynomial) : (shift n p).length = n+p.length := by
  induction n with
  | zero => simp [shift]
  | succ n ih => simp [shift, ih, Nat.succ_add]

theorem shift_scale (n c : Nat) (p : Polynomial) : scale c (shift n p) = shift n (scale c p) := by
  induction n with
  | zero => simp [shift]
  | succ n ih => simpa [shift, scale] using congrArg (List.cons 0) ih

end JonnyLean.Polynomials
