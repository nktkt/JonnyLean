import JonnyLean.NumberTheory.Divisibility

namespace JonnyLean

theorem divides_add (d a b : Nat) (ha : Divides d a) (hb : Divides d b) :
    Divides d (a + b) := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  exact ⟨i + j, by rw [hi, hj, Nat.mul_add]⟩

theorem divides_linear_combination (d a b x y : Nat)
    (ha : Divides d a) (hb : Divides d b) : Divides d (a * x + b * y) :=
  divides_add d (a * x) (b * y) (divides_mul_right d a x ha) (divides_mul_right d b y hb)

theorem divides_sub (d a b : Nat) (ha : Divides d a) (hb : Divides d b) :
    Divides d (a - b) := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  exact ⟨i - j, by rw [hi, hj, Nat.mul_sub_left_distrib]⟩

theorem divides_add_cancel_left (d a b : Nat) (ha : Divides d a)
    (hab : Divides d (a + b)) : Divides d b := by
  have h := divides_sub d (a + b) a hab ha
  simpa using h

theorem divides_add_iff_right (d a b : Nat) (ha : Divides d a) :
    Divides d (a + b) ↔ Divides d b := by
  constructor
  · exact divides_add_cancel_left d a b ha
  · exact divides_add d a b ha

end JonnyLean
