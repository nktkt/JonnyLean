import Std

namespace JonnyLean.Arithmetic

def listLcm : List Nat → Nat
  | [] => 1
  | a :: xs => Nat.lcm a (listLcm xs)

theorem listLcm_dvd (xs : List Nat) (d : Nat) :
    listLcm xs ∣ d ↔ ∀ a ∈ xs, a ∣ d := by
  induction xs with
  | nil => simp [listLcm]
  | cons a xs ih => simp only [listLcm, Nat.lcm_dvd_iff, ih, List.mem_cons,
      forall_eq_or_imp]

theorem listLcm_append (xs ys : List Nat) :
    listLcm (xs ++ ys) = Nat.lcm (listLcm xs) (listLcm ys) := by
  induction xs with
  | nil => simp [listLcm]
  | cons a xs ih => simp [listLcm, ih, Nat.lcm_assoc]

theorem member_dvd_listLcm (xs : List Nat) (a : Nat) (h : a ∈ xs) : a ∣ listLcm xs :=
  (listLcm_dvd xs _).1 (Nat.dvd_refl _) a h

theorem listLcm_eq_zero (xs : List Nat) : listLcm xs = 0 ↔ 0 ∈ xs := by
  induction xs with
  | nil => simp [listLcm]
  | cons a xs ih => simp only [listLcm, Nat.lcm_eq_zero_iff, ih, List.mem_cons, eq_comm (a := 0) (b := a)]

end JonnyLean.Arithmetic
