import JonnyLean.Arithmetic.Product

namespace JonnyLean.Arithmetic

theorem gcd_product_eq_one (a : Nat) (xs : List Nat)
    (h : ∀ b ∈ xs, Nat.gcd a b = 1) : Nat.gcd a (product xs) = 1 := by
  induction xs with
  | nil => simp [product]
  | cons b xs ih =>
    rw [product, Nat.gcd_mul_right_right_of_gcd_eq_one (h b (by simp))]
    exact ih (fun c hc => h c (List.mem_cons_of_mem b hc))

theorem gcd_product_eq_one_iff (a : Nat) (xs : List Nat) :
    Nat.gcd a (product xs) = 1 ↔ ∀ b ∈ xs, Nat.gcd a b = 1 := by
  constructor
  · intro h b hb
    apply Nat.dvd_one.mp
    rw [← h]
    exact Nat.gcd_dvd_gcd_of_dvd_right a (member_dvd_product xs b hb)
  · exact gcd_product_eq_one a xs

theorem gcd_product_append (a : Nat) (xs ys : List Nat) :
    Nat.gcd a (product (xs ++ ys)) = 1 ↔
      Nat.gcd a (product xs) = 1 ∧ Nat.gcd a (product ys) = 1 := by
  simp only [gcd_product_eq_one_iff, List.mem_append, or_imp, forall_and]

theorem gcd_product_powers (a n : Nat) (xs : List Nat)
    (h : ∀ b ∈ xs, Nat.gcd a b = 1) : Nat.gcd a ((product xs)^n) = 1 :=
  Nat.gcd_pow_right_of_gcd_eq_one (gcd_product_eq_one a xs h)

end JonnyLean.Arithmetic
