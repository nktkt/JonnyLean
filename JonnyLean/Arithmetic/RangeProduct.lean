import Std

namespace JonnyLean.Arithmetic

def rangeProduct (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n+1 => rangeProduct f n * f n

theorem rangeProduct_split (f : Nat → Nat) (m n : Nat) :
    rangeProduct f (m+n) = rangeProduct f m * rangeProduct (fun i => f (m+i)) n := by
  induction n with
  | zero => simp [rangeProduct]
  | succ n ih => simp [rangeProduct, ih, Nat.mul_assoc]

theorem rangeProduct_mul (f g : Nat → Nat) (n : Nat) :
    rangeProduct (fun i => f i*g i) n = rangeProduct f n*rangeProduct g n := by
  induction n with
  | zero => simp [rangeProduct]
  | succ n ih => simp only [rangeProduct, ih]; ac_rfl

theorem rangeProduct_const (c n : Nat) : rangeProduct (fun _ => c) n = c^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rangeProduct, ih, Nat.pow_succ]

theorem rangeProduct_dvd (f g : Nat → Nat) (n : Nat)
    (h : ∀ i, i < n → f i ∣ g i) : rangeProduct f n ∣ rangeProduct g n := by
  induction n with
  | zero => exact Nat.dvd_refl 1
  | succ n ih =>
    exact Nat.mul_dvd_mul (ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n))))
      (h n (Nat.lt_succ_self n))

end JonnyLean.Arithmetic
