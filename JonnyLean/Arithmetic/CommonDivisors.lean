import JonnyLean.Arithmetic.GcdList
import JonnyLean.Arithmetic.LcmList
import JonnyLean.Arithmetic.Product

namespace JonnyLean.Arithmetic

theorem listLcm_dvd_product (xs : List Nat) : listLcm xs ∣ product xs := by
  apply (listLcm_dvd xs _).2
  exact fun a ha => member_dvd_product xs a ha

theorem listGcd_dvd_listLcm (a : Nat) (xs : List Nat) :
    listGcd (a::xs) ∣ listLcm (a::xs) :=
  Nat.dvd_trans (listGcd_dvd_member (a::xs) a (by simp))
    (member_dvd_listLcm (a::xs) a (by simp))

theorem listGcd_listLcm_absorb (a : Nat) (xs : List Nat) :
    Nat.gcd (listGcd (a::xs)) (listLcm (a::xs)) = listGcd (a::xs) :=
  Nat.gcd_eq_left (listGcd_dvd_listLcm a xs)

theorem common_dvd_product (d a : Nat) (xs : List Nat)
    (h : ∀ b ∈ a::xs, d ∣ b) : d ∣ product (a::xs) :=
  Nat.dvd_trans (h a (by simp)) (member_dvd_product (a::xs) a (by simp))

theorem common_multiple_product (xs : List Nat) (n : Nat) :
    listLcm xs ∣ n ↔ ∀ a ∈ xs, a ∣ n := listLcm_dvd xs n

end JonnyLean.Arithmetic
