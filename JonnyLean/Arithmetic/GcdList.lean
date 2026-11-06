import Std

namespace JonnyLean.Arithmetic

def listGcd : List Nat → Nat
  | [] => 0
  | a :: xs => Nat.gcd a (listGcd xs)

theorem dvd_listGcd (d : Nat) (xs : List Nat) :
    d ∣ listGcd xs ↔ ∀ a ∈ xs, d ∣ a := by
  induction xs with
  | nil => simp [listGcd]
  | cons a xs ih => simp only [listGcd, Nat.dvd_gcd_iff, ih, List.mem_cons,
      forall_eq_or_imp]

theorem listGcd_append (xs ys : List Nat) :
    listGcd (xs ++ ys) = Nat.gcd (listGcd xs) (listGcd ys) := by
  induction xs with
  | nil => simp [listGcd]
  | cons a xs ih => simp [listGcd, ih, Nat.gcd_assoc]

theorem listGcd_dvd_member (xs : List Nat) (a : Nat) (h : a ∈ xs) : listGcd xs ∣ a :=
  (dvd_listGcd _ xs).1 (Nat.dvd_refl _) a h

theorem listGcd_scale (k : Nat) (xs : List Nat) :
    listGcd (xs.map (fun a => k*a)) = k * listGcd xs := by
  induction xs with
  | nil => simp [listGcd]
  | cons a xs ih => simp [listGcd, ih, Nat.gcd_mul_left]

theorem listGcd_eq_zero (xs : List Nat) : listGcd xs = 0 ↔ ∀ a ∈ xs, a = 0 := by
  induction xs with
  | nil => simp [listGcd]
  | cons a xs ih => simp [listGcd, ih]

end JonnyLean.Arithmetic
