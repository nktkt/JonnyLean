import JonnyLean.Arithmetic.ReducedPair

namespace JonnyLean.Arithmetic

theorem primitive_scale_gcd (a b k : Nat) (h : Nat.gcd a b = 1) :
    Nat.gcd (k*a) (k*b) = k := by rw [Nat.gcd_mul_left, h, Nat.mul_one]

theorem primitive_scale_reduced (a b k : Nat) (h : Nat.gcd a b = 1) (hk : 0 < k) :
    reducedPair (k*a) (k*b) = (a,b) := by
  simp [reducedPair, primitive_scale_gcd a b k h, Nat.mul_div_cancel_left _ hk]

theorem primitive_scale_unique (a b c d k l : Nat)
    (hab : Nat.gcd a b = 1) (hcd : Nat.gcd c d = 1)
    (h₁ : k*a = l*c) (h₂ : k*b = l*d) : k = l := by
  calc
    k = Nat.gcd (k*a) (k*b) := (primitive_scale_gcd a b k hab).symm
    _ = Nat.gcd (l*c) (l*d) := by rw [h₁,h₂]
    _ = l := primitive_scale_gcd c d l hcd

theorem primitive_scale_lcm (a b k : Nat) (h : Nat.gcd a b = 1) :
    Nat.lcm (k*a) (k*b) = k*(a*b) := by
  rw [Nat.lcm_mul_left, Nat.lcm_eq_mul_div, h, Nat.div_one]

end JonnyLean.Arithmetic
