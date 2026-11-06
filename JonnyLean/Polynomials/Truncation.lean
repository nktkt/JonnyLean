import JonnyLean.Polynomials.Evaluation

namespace JonnyLean.Polynomials

theorem evaluate_truncate (p : Polynomial) (n x : Nat) :
    evaluate p x = evaluate (p.take n) x + x^n * evaluate (p.drop n) x := by
  induction n generalizing p with
  | zero => simp [evaluate]
  | succ n ih =>
    cases p with
    | nil => simp [evaluate]
    | cons a p =>
      simp only [List.take_succ_cons, List.drop_succ_cons, evaluate, Nat.pow_succ]
      rw [ih p]
      simp only [Nat.mul_add, Nat.mul_assoc]
      ac_rfl

theorem evaluate_take_le (p : Polynomial) (n x : Nat) :
    evaluate (p.take n) x ≤ evaluate p x := by
  rw [evaluate_truncate p n x]
  exact Nat.le_add_right _ _

theorem evaluate_drop_dvd_difference (p : Polynomial) (n x : Nat) :
    x^n ∣ evaluate p x - evaluate (p.take n) x := by
  refine ⟨evaluate (p.drop n) x, ?_⟩
  rw [evaluate_truncate p n x, Nat.add_sub_cancel_left]

theorem evaluate_take_mod (p : Polynomial) (n x : Nat) :
    evaluate p x % x^n = evaluate (p.take n) x % x^n := by
  rw [evaluate_truncate p n x]
  simp

end JonnyLean.Polynomials
