import Std

namespace JonnyLean.Arithmetic

def radixValue (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + b * radixValue b ds

def radixResidue (m b : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => (d + b * radixResidue m b ds) % m

theorem radixResidue_correct (m b : Nat) (ds : List Nat) :
    radixResidue m b ds = radixValue b ds % m := by
  induction ds with
  | nil => simp [radixResidue, radixValue]
  | cons d ds ih => simp [radixResidue, radixValue, ih, Nat.add_mod, Nat.mul_mod]

theorem radixResidue_bounded (m b : Nat) (ds : List Nat) (hm : 0 < m) :
    radixResidue m b ds < m := by
  rw [radixResidue_correct]
  exact Nat.mod_lt _ hm

theorem radixValue_append (b : Nat) (xs ys : List Nat) :
    radixValue b (xs ++ ys) = radixValue b xs + b^xs.length * radixValue b ys := by
  induction xs with
  | nil => simp [radixValue]
  | cons a xs ih =>
    simp only [List.cons_append, radixValue, ih, List.length_cons, Nat.pow_succ,
      Nat.mul_add, Nat.mul_assoc]
    ac_rfl

theorem radixResidue_append (m b : Nat) (xs ys : List Nat) :
    radixResidue m b (xs ++ ys) =
      (radixResidue m b xs + b^xs.length * radixResidue m b ys) % m := by
  simp only [radixResidue_correct, radixValue_append, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

end JonnyLean.Arithmetic
