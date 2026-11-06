import Std

namespace JonnyLean.Arithmetic

def lcmTriple (a b c : Nat) : Nat := Nat.lcm a (Nat.lcm b c)

theorem lcmTriple_dvd (a b c d : Nat) :
    lcmTriple a b c ∣ d ↔ a ∣ d ∧ b ∣ d ∧ c ∣ d := by
  simp only [lcmTriple, Nat.lcm_dvd_iff]

theorem lcmTriple_scale (k a b c : Nat) :
    lcmTriple (k*a) (k*b) (k*c) = k*lcmTriple a b c := by
  simp only [lcmTriple, Nat.lcm_mul_left]

theorem lcmTriple_one (a b : Nat) : lcmTriple a b 1 = Nat.lcm a b := by
  simp [lcmTriple]

theorem lcmTriple_unique (a b c l : Nat)
    (hl : ∀ d, l ∣ d ↔ a ∣ d ∧ b ∣ d ∧ c ∣ d) : l = lcmTriple a b c := by
  apply Nat.dvd_antisymm
  · exact (hl _).2 ((lcmTriple_dvd a b c _).1 (Nat.dvd_refl _))
  · exact (lcmTriple_dvd a b c l).2 ((hl l).1 (Nat.dvd_refl l))

end JonnyLean.Arithmetic
