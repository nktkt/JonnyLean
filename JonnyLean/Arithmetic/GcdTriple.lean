import Std

namespace JonnyLean.Arithmetic

def gcdTriple (a b c : Nat) : Nat := Nat.gcd a (Nat.gcd b c)

theorem dvd_gcdTriple (d a b c : Nat) :
    d ∣ gcdTriple a b c ↔ d ∣ a ∧ d ∣ b ∧ d ∣ c := by
  simp only [gcdTriple, Nat.dvd_gcd_iff]

theorem gcdTriple_rotate (a b c : Nat) : gcdTriple a b c = gcdTriple b c a := by
  unfold gcdTriple
  rw [← Nat.gcd_assoc, Nat.gcd_comm a b, Nat.gcd_assoc,
    Nat.gcd_comm a c]

theorem gcdTriple_scale (k a b c : Nat) :
    gcdTriple (k*a) (k*b) (k*c) = k * gcdTriple a b c := by
  simp only [gcdTriple, Nat.gcd_mul_left]

theorem gcdTriple_zero (a b : Nat) : gcdTriple a b 0 = Nat.gcd a b := by
  simp [gcdTriple]

theorem gcdTriple_unique (a b c g : Nat)
    (hg : ∀ d, d ∣ g ↔ d ∣ a ∧ d ∣ b ∧ d ∣ c) : g = gcdTriple a b c := by
  apply Nat.dvd_antisymm
  · exact (dvd_gcdTriple g a b c).2 ((hg g).1 (Nat.dvd_refl g))
  · exact (hg _).2 ((dvd_gcdTriple _ a b c).1 (Nat.dvd_refl _))

end JonnyLean.Arithmetic
