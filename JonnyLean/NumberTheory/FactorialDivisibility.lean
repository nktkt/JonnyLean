import JonnyLean.NumberTheory.Factorial
import JonnyLean.NumberTheory.Divisibility

namespace JonnyLean

/-- Product of the n successive factors a+1 through a+n. -/
def risingProduct (a : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => risingProduct a n * (a + n + 1)

theorem factorial_add_product (a n : Nat) :
    factorial (a + n) = factorial a * risingProduct a n := by
  induction n with
  | zero => simp [risingProduct]
  | succ n ih =>
    rw [Nat.add_succ]
    simp only [factorial, risingProduct, ih]
    ac_rfl

theorem factorial_divides_later (m n : Nat) (h : m ≤ n) :
    Divides (factorial m) (factorial n) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  exact ⟨risingProduct m k, by rw [hk, factorial_add_product]⟩

theorem input_divides_factorial (n : Nat) : Divides (n + 1) (factorial (n + 1)) :=
  ⟨factorial n, rfl⟩

theorem positive_le_divides_factorial (k n : Nat) (hk : 0 < k) (hkn : k ≤ n) :
    Divides k (factorial n) := by
  cases k with
  | zero => exact False.elim (Nat.not_lt_zero 0 hk)
  | succ k =>
    exact divides_trans (k + 1) (factorial (k + 1)) (factorial n)
      (input_divides_factorial k) (factorial_divides_later (k + 1) n hkn)

theorem rising_product_positive (a n : Nat) : 0 < risingProduct a n := by
  induction n with
  | zero => simp [risingProduct]
  | succ n ih => exact Nat.mul_pos ih (by omega)

theorem rising_product_split (a m n : Nat) :
    risingProduct a (m + n) = risingProduct a m * risingProduct (a + m) n := by
  induction n with
  | zero => simp [risingProduct]
  | succ n ih =>
    rw [Nat.add_succ]
    simp only [risingProduct, ih, Nat.add_assoc, Nat.mul_assoc]

end JonnyLean
