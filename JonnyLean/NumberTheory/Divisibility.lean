import Std

namespace JonnyLean

/-- Divisibility with a concrete multiplier, oriented for witness calculations. -/
def Divides (d n : Nat) : Prop := ∃ k, n = d * k

theorem divides_refl (n : Nat) : Divides n n := ⟨1, (Nat.mul_one n).symm⟩

theorem divides_trans (a b c : Nat) (hab : Divides a b) (hbc : Divides b c) :
    Divides a c := by
  obtain ⟨i, hi⟩ := hab
  obtain ⟨j, hj⟩ := hbc
  exact ⟨i * j, by rw [hj, hi, Nat.mul_assoc]⟩

theorem divides_mul_right (d n k : Nat) (h : Divides d n) : Divides d (n * k) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i * k, by rw [hi, Nat.mul_assoc]⟩

theorem divides_mul_left (d n k : Nat) (h : Divides d n) : Divides d (k * n) := by
  rw [Nat.mul_comm]
  exact divides_mul_right d n k h

theorem divides_product (a b c d : Nat) (hac : Divides a c) (hbd : Divides b d) :
    Divides (a * b) (c * d) := by
  obtain ⟨i, hi⟩ := hac
  obtain ⟨j, hj⟩ := hbd
  refine ⟨i * j, ?_⟩
  rw [hi, hj]
  simp only [Nat.mul_comm, Nat.mul_left_comm]

theorem zero_divides_iff (n : Nat) : Divides 0 n ↔ n = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    simpa using hk
  · intro h
    exact ⟨0, h⟩

end JonnyLean
