import JonnyLean.NumberTheory.Congruence

namespace JonnyLean

theorem congruent_add (m a b c d : Nat) (hab : Congruent m a b)
    (hcd : Congruent m c d) : Congruent m (a + c) (b + d) := by
  unfold Congruent at *
  rw [Nat.add_mod, Nat.add_mod b d, hab, hcd]

theorem congruent_mul (m a b c d : Nat) (hab : Congruent m a b)
    (hcd : Congruent m c d) : Congruent m (a * c) (b * d) := by
  unfold Congruent at *
  rw [Nat.mul_mod, Nat.mul_mod b d, hab, hcd]

theorem congruent_pow (m a b n : Nat) (hab : Congruent m a b) :
    Congruent m (a ^ n) (b ^ n) := by
  induction n with
  | zero => exact congruent_refl m 1
  | succ n ih =>
    simp only [Nat.pow_succ]
    exact congruent_mul m (a ^ n) (b ^ n) a b ih hab

theorem congruent_affine (m a b u v : Nat) (h : Congruent m a b) :
    Congruent m (u * a + v) (u * b + v) :=
  congruent_add m (u * a) (u * b) v v
    (congruent_mul m u u a b (congruent_refl m u) h) (congruent_refl m v)

theorem congruent_quadratic (m a b u v w : Nat) (h : Congruent m a b) :
    Congruent m (u * a ^ 2 + v * a + w) (u * b ^ 2 + v * b + w) := by
  apply congruent_add
  · apply congruent_add
    · exact congruent_mul m u u (a ^ 2) (b ^ 2) (congruent_refl m u) (congruent_pow m a b 2 h)
    · exact congruent_mul m v v a b (congruent_refl m v) h
  · exact congruent_refl m w

end JonnyLean
