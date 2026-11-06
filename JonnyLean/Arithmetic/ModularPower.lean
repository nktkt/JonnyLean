import Std

namespace JonnyLean.Arithmetic

def modularPower (m a : Nat) : Nat → Nat
  | 0 => 1 % m
  | n+1 => (modularPower m a n * a) % m

theorem modularPower_correct (m a n : Nat) : modularPower m a n = a^n % m := by
  induction n with
  | zero => simp [modularPower]
  | succ n ih => simp [modularPower, ih, Nat.pow_succ, Nat.mul_mod]

theorem modularPower_bounded (m a n : Nat) (hm : 0 < m) : modularPower m a n < m := by
  rw [modularPower_correct]
  exact Nat.mod_lt _ hm

theorem modularPower_add (m a n k : Nat) :
    modularPower m a (n+k) = (modularPower m a n * modularPower m a k) % m := by
  simp only [modularPower_correct, Nat.pow_add, Nat.mul_mod, Nat.mod_mod]

theorem modularPower_input (m a n : Nat) : modularPower m (a%m) n = modularPower m a n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [modularPower, ih, Nat.mul_mod]

theorem modularPower_zero_modulus (a n : Nat) : modularPower 0 a n = a^n := by
  simp [modularPower_correct]

end JonnyLean.Arithmetic
