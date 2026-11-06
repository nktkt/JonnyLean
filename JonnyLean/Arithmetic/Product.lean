import Std

namespace JonnyLean.Arithmetic

def product : List Nat → Nat
  | [] => 1
  | a :: xs => a * product xs

theorem product_append (xs ys : List Nat) : product (xs ++ ys) = product xs * product ys := by
  induction xs with
  | nil => simp [product]
  | cons a xs ih => simp [product, ih, Nat.mul_assoc]

theorem product_eq_zero (xs : List Nat) : product xs = 0 ↔ 0 ∈ xs := by
  induction xs with
  | nil => simp [product]
  | cons a xs ih => simp only [product, Nat.mul_eq_zero, ih, List.mem_cons, eq_comm (a := 0) (b := a)]

theorem member_dvd_product (xs : List Nat) (a : Nat) (h : a ∈ xs) : a ∣ product xs := by
  induction xs with
  | nil => simp at h
  | cons b xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_trans (ih h) (Nat.dvd_mul_left _ _)

theorem product_positive (xs : List Nat) : 0 < product xs ↔ ∀ a ∈ xs, 0 < a := by
  induction xs with
  | nil => simp [product]
  | cons a xs ih =>
    simp only [product, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h
      exact ⟨Nat.pos_of_mul_pos_right h, ih.mp (Nat.pos_of_mul_pos_left h)⟩
    · rintro ⟨ha, hx⟩
      exact Nat.mul_pos ha (ih.mpr hx)

theorem product_singleton (a : Nat) : product [a] = a := by simp [product]

end JonnyLean.Arithmetic
