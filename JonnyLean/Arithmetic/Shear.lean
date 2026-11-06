import Std

namespace JonnyLean.Arithmetic

def shear (k : Nat) (s : Nat × Nat) : Nat × Nat := (s.2, s.1 + k*s.2)

def shearTrace : List Nat → Nat × Nat → Nat × Nat
  | [], s => s
  | k :: ks, s => shearTrace ks (shear k s)

theorem shear_gcd (k : Nat) (s : Nat × Nat) :
    Nat.gcd (shear k s).1 (shear k s).2 = Nat.gcd s.1 s.2 := by
  simp [shear, Nat.gcd_comm]

theorem shearTrace_gcd (ks : List Nat) (s : Nat × Nat) :
    Nat.gcd (shearTrace ks s).1 (shearTrace ks s).2 = Nat.gcd s.1 s.2 := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih => rw [shearTrace, ih, shear_gcd]

theorem shearTrace_append (ks ls : List Nat) (s : Nat × Nat) :
    shearTrace (ks ++ ls) s = shearTrace ls (shearTrace ks s) := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih => exact ih (shear k s)

theorem shearTrace_common (ks : List Nat) (s : Nat × Nat) (d : Nat) :
    (d ∣ (shearTrace ks s).1 ∧ d ∣ (shearTrace ks s).2) ↔
    (d ∣ s.1 ∧ d ∣ s.2) := by
  rw [← Nat.dvd_gcd_iff, shearTrace_gcd, Nat.dvd_gcd_iff]

end JonnyLean.Arithmetic
