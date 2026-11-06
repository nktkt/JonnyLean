import JonnyLean.Arithmetic.ProductMap

namespace JonnyLean.Arithmetic

theorem product_map_dvd (f g : α → Nat) (xs : List α)
    (h : ∀ a ∈ xs, f a ∣ g a) : product (xs.map f) ∣ product (xs.map g) := by
  induction xs with
  | nil => exact Nat.dvd_refl 1
  | cons a xs ih =>
    exact Nat.mul_dvd_mul (h a (by simp)) (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem product_map_quotient (d : Nat) (xs : List Nat)
    (h : ∀ a ∈ xs, d ∣ a) :
    d^xs.length * product (xs.map (fun a => a/d)) = product xs := by
  induction xs with
  | nil => simp [product]
  | cons a xs ih =>
    simp only [List.length_cons, Nat.pow_succ, List.map_cons, product]
    calc
      d^xs.length*d*(a/d*product (xs.map (fun a => a/d))) =
          (d*(a/d))*(d^xs.length*product (xs.map (fun a => a/d))) := by ac_rfl
      _ = a*product xs := by
        rw [Nat.mul_div_cancel' (h a (by simp)), ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem uniform_power_dvd_product (d : Nat) (xs : List Nat)
    (h : ∀ a ∈ xs, d ∣ a) : d^xs.length ∣ product xs :=
  ⟨product (xs.map (fun a => a/d)), (product_map_quotient d xs h).symm⟩

theorem product_dvd_append_left (xs ys : List Nat) : product xs ∣ product (xs++ys) := by
  rw [product_append]
  exact Nat.dvd_mul_right _ _

end JonnyLean.Arithmetic
