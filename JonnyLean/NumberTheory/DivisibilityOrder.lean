import JonnyLean.NumberTheory.Divisibility

namespace JonnyLean

theorem divisor_le (d n : Nat) (hn : 0 < n) (h : Divides d n) : d ≤ n := by
  obtain ⟨k, hk⟩ := h
  have hkpos : 0 < k := by
    cases k with
    | zero => simp at hk; omega
    | succ k => omega
  rw [hk]
  exact Nat.le_mul_of_pos_right d hkpos

theorem divides_antisymm (a b : Nat) (hab : Divides a b) (hba : Divides b a) : a = b := by
  cases a with
  | zero => exact ((zero_divides_iff b).mp hab).symm
  | succ a =>
    have hb : 0 < b := by
      cases b with
      | zero => have h := (zero_divides_iff (a + 1)).mp hba; omega
      | succ b => omega
    exact Nat.le_antisymm (divisor_le (a + 1) b hb hab) (divisor_le b (a + 1) (by omega) hba)

theorem divides_one_iff (d : Nat) : Divides d 1 ↔ d = 1 := by
  constructor
  · intro h
    have hle := divisor_le d 1 (by decide) h
    cases d with
    | zero => have hz := (zero_divides_iff 1).mp h; omega
    | succ d => omega
  · intro h
    subst d
    exact divides_refl 1

theorem divisor_positive (d n : Nat) (hn : 0 < n) (h : Divides d n) : 0 < d := by
  cases d with
  | zero => have hz := (zero_divides_iff n).mp h; omega
  | succ d => omega

theorem divisor_eq_of_large (d n : Nat) (hn : 0 < n) (h : Divides d n)
    (hlarge : n < 2 * d) : d = n := by
  obtain ⟨k, hk⟩ := h
  have hklt : k < 2 := by
    by_cases htwo : 2 ≤ k
    · have hmul := Nat.mul_le_mul_left d htwo
      omega
    · omega
  have hkone : k = 1 := by
    cases k with
    | zero => simp at hk; omega
    | succ k => omega
  simpa [hkone] using hk.symm

end JonnyLean
