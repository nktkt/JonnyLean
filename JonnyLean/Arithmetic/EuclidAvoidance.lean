import JonnyLean.Arithmetic.Product

namespace JonnyLean.Arithmetic

def avoidance (xs : List Nat) (k : Nat) : Nat := product xs*k+1

theorem avoidance_coprime (xs : List Nat) (k : Nat) :
    Nat.gcd (product xs) (avoidance xs k) = 1 := by
  simp [avoidance, Nat.add_comm]

theorem avoidance_member_coprime (xs : List Nat) (k a : Nat) (ha : a ∈ xs) :
    Nat.gcd a (avoidance xs k) = 1 := by
  apply Nat.dvd_one.mp
  rw [← avoidance_coprime xs k]
  exact Nat.gcd_dvd_gcd_of_dvd_left _ (member_dvd_product xs a ha)

theorem avoidance_not_dvd (xs : List Nat) (k a : Nat) (ha : a ∈ xs) (h : 1 < a) :
    ¬ a ∣ avoidance xs k := by
  intro hd
  have hg := avoidance_member_coprime xs k a ha
  rw [Nat.gcd_eq_left hd] at hg
  omega

theorem avoidance_positive (xs : List Nat) (k : Nat) : 0 < avoidance xs k :=
  Nat.succ_pos _

end JonnyLean.Arithmetic
