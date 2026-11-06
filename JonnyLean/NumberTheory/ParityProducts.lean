import JonnyLean.NumberTheory.OddSums

namespace JonnyLean

theorem even_mul_right (a b : Nat) (ha : Even a) : Even (a * b) := by
  obtain ⟨k, hk⟩ := ha
  exact ⟨k * b, by rw [hk, Nat.mul_assoc]⟩

theorem even_mul_left (a b : Nat) (hb : Even b) : Even (a * b) := by
  rw [Nat.mul_comm]
  exact even_mul_right b a hb

theorem odd_mul_odd (a b : Nat) (ha : Odd a) (hb : Odd b) : Odd (a * b) := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨2 * i * j + i + j, ?_⟩
  rw [hi, hj]
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  ac_rfl

theorem even_pow_succ (a n : Nat) (ha : Even a) : Even (a ^ (n + 1)) := by
  rw [Nat.pow_succ]
  exact even_mul_left (a ^ n) a ha

theorem odd_pow (a n : Nat) (ha : Odd a) : Odd (a ^ n) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [Nat.pow_succ]
    exact odd_mul_odd (a ^ n) a ih ha

theorem even_square_iff (n : Nat) : Even (n * n) ↔ Even n := by
  constructor
  · intro h
    cases even_or_odd n with
    | inl hn => exact hn
    | inr hn => exact False.elim (not_even_and_odd (n * n) ⟨h, odd_mul_odd n n hn hn⟩)
  · exact even_mul_right n n

end JonnyLean
