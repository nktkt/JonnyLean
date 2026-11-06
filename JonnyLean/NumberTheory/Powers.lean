import JonnyLean.NumberTheory.Divisibility

namespace JonnyLean

theorem power_divides_later (a m n : Nat) (h : m ≤ n) : Divides (a ^ m) (a ^ n) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  exact ⟨a ^ k, by rw [hk, Nat.pow_add]⟩

theorem divides_power (a b n : Nat) (h : Divides a b) : Divides (a ^ n) (b ^ n) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k ^ n, by rw [hk, Nat.mul_pow]⟩

theorem base_divides_positive_power (a n : Nat) : Divides a (a ^ (n + 1)) := by
  refine ⟨a ^ n, ?_⟩
  rw [Nat.pow_succ, Nat.mul_comm]

theorem power_even_exponent (a n : Nat) : a ^ (2 * n) = (a ^ n) * (a ^ n) := by
  rw [Nat.two_mul, Nat.pow_add]

theorem power_monotone_exponent (a m n : Nat) (ha : 0 < a) (h : m ≤ n) :
    a ^ m ≤ a ^ n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  rw [hk, Nat.pow_add]
  exact Nat.le_mul_of_pos_right (a ^ m) (Nat.pow_pos ha)

theorem power_successor_lower_bound (a n : Nat) (ha : 0 < a) : a ≤ a ^ (n + 1) := by
  have h := power_monotone_exponent a 1 (n + 1) ha (by omega)
  simpa using h

end JonnyLean
