import Std

namespace JonnyLean.Arithmetic

def reducedPair (a b : Nat) : Nat × Nat := (a / Nat.gcd a b, b / Nat.gcd a b)

theorem reducedPair_reconstruct_left (a b : Nat) :
    Nat.gcd a b * (reducedPair a b).1 = a := by
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)

theorem reducedPair_reconstruct_right (a b : Nat) :
    Nat.gcd a b * (reducedPair a b).2 = b := by
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)

theorem reducedPair_coprime (a b : Nat) (h : 0 < a ∨ 0 < b) :
    Nat.gcd (reducedPair a b).1 (reducedPair a b).2 = 1 := by
  rcases h with ha | hb
  · exact Nat.gcd_div_gcd_div_gcd_of_pos_left ha
  · exact Nat.gcd_div_gcd_div_gcd_of_pos_right hb

theorem reducedPair_of_coprime (a b : Nat) (h : Nat.gcd a b = 1) :
    reducedPair a b = (a,b) := by simp [reducedPair, h]

theorem reducedPair_zero : reducedPair 0 0 = (0,0) := rfl

end JonnyLean.Arithmetic
