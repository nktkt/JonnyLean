import Std

namespace JonnyLean.Arithmetic

theorem coprime_cancel (a b c : Nat) (h : Nat.gcd a b = 1) :
    a ∣ b*c ↔ a ∣ c := by
  have e := @Nat.dvd_gcd_mul_iff_dvd_mul a b c
  simpa [h] using e.symm

theorem coprime_cancel_power (a b c n : Nat) (h : Nat.gcd a b = 1) :
    a ∣ b^n*c ↔ a ∣ c :=
  coprime_cancel a (b^n) c (Nat.gcd_pow_right_of_gcd_eq_one h)

theorem coprime_two_factors (a b c : Nat) (h : Nat.gcd a b = 1)
    (ha : a ∣ c) (hb : b ∣ c) : a*b ∣ c := by
  obtain ⟨k, hk⟩ := ha
  rw [hk] at hb ⊢
  have hba : Nat.gcd b a = 1 := by simpa [Nat.gcd_comm] using h
  obtain ⟨j, hj⟩ := (coprime_cancel b a k hba).1 hb
  exact ⟨j, by rw [hj, Nat.mul_assoc]⟩

theorem coprime_product_dvd_iff (a b c : Nat) (h : Nat.gcd a b = 1) :
    a*b ∣ c ↔ a ∣ c ∧ b ∣ c := by
  constructor
  · intro hd
    exact ⟨Nat.dvd_trans (Nat.dvd_mul_right a b) hd,
      Nat.dvd_trans (Nat.dvd_mul_left b a) hd⟩
  · rintro ⟨ha,hb⟩
    exact coprime_two_factors a b c h ha hb

end JonnyLean.Arithmetic
