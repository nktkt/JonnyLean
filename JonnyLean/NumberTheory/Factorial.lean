import Std

namespace JonnyLean

/-- The empty product is one. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem factorial_positive (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (by omega) ih

theorem factorial_one_le (n : Nat) : 1 ≤ factorial n := by
  have h := factorial_positive n
  omega

theorem factorial_step_le (n : Nat) : factorial n ≤ factorial (n + 1) := by
  change factorial n ≤ (n + 1) * factorial n
  rw [Nat.mul_comm]
  exact Nat.le_mul_of_pos_right _ (by omega)

theorem factorial_mono (m n : Nat) (h : m ≤ n) : factorial m ≤ factorial n := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact Nat.le_refl _
  | succ n ih =>
    by_cases hmn : m ≤ n
    · exact Nat.le_trans (ih hmn) (factorial_step_le n)
    · have hm : m = n + 1 := by omega
      subst m
      exact Nat.le_refl _

theorem factorial_ge_input (n : Nat) : n ≤ factorial n := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => exact Nat.le_mul_of_pos_right (n + 1) (factorial_positive n)

theorem factorial_strict_step (n : Nat) (h : 0 < n) : factorial n < factorial (n + 1) := by
  change factorial n < (n + 1) * factorial n
  rw [Nat.add_mul, Nat.one_mul]
  have hp := Nat.mul_pos h (factorial_positive n)
  omega

end JonnyLean
