import Std

namespace JonnyLean

/-- Equality of remainders; modulus zero is permitted and gives equality. -/
def Congruent (m a b : Nat) : Prop := a % m = b % m

theorem congruent_refl (m a : Nat) : Congruent m a a := rfl

theorem congruent_symm (m a b : Nat) (h : Congruent m a b) : Congruent m b a := h.symm

theorem congruent_trans (m a b c : Nat) (hab : Congruent m a b)
    (hbc : Congruent m b c) : Congruent m a c := hab.trans hbc

theorem congruent_remainder (m a : Nat) : Congruent m a (a % m) := by
  unfold Congruent
  simp

theorem congruent_zero_modulus (a b : Nat) : Congruent 0 a b ↔ a = b := by
  simp [Congruent]

theorem congruent_add_multiple (m a k : Nat) : Congruent m (a + m * k) a := by
  unfold Congruent
  simp

theorem congruent_small_iff (m a b : Nat) (ha : a < m) (hb : b < m) :
    Congruent m a b ↔ a = b := by
  unfold Congruent
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem congruent_unique_remainder (m a r : Nat) (hr : r < m)
    (h : Congruent m a r) : r = a % m := by
  unfold Congruent at h
  rw [Nat.mod_eq_of_lt hr] at h
  exact h.symm

end JonnyLean
