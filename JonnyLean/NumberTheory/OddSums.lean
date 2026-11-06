import Std
import JonnyLean.NumberTheory.Parity

namespace JonnyLean

/-- Oddness is given by an explicit natural-number witness. -/
def Odd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

theorem even_succ_odd (n : Nat) (h : Even n) : Odd (n + 1) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [hk]⟩

theorem odd_succ_even (n : Nat) (h : Odd n) : Even (n + 1) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by omega⟩

theorem even_add_odd (a b : Nat) (ha : Even a) (hb : Odd b) : Odd (a + b) := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  exact ⟨i + j, by rw [hi, hj, Nat.mul_add]; omega⟩

theorem odd_add_even (a b : Nat) (ha : Odd a) (hb : Even b) : Odd (a + b) := by
  rw [Nat.add_comm]
  exact even_add_odd b a hb ha

theorem odd_add_odd (a b : Nat) (ha : Odd a) (hb : Odd b) : Even (a + b) := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  exact ⟨i + j + 1, by rw [hi, hj]; simp only [Nat.mul_add]; omega⟩

theorem even_or_odd (n : Nat) : Even n ∨ Odd n := by
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ n ih =>
    cases ih with
    | inl h => exact Or.inr (even_succ_odd n h)
    | inr h => exact Or.inl (odd_succ_even n h)

theorem not_even_and_odd (n : Nat) : ¬ (Even n ∧ Odd n) := by
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  omega

end JonnyLean
