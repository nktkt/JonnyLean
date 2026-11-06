import JonnyLean.Arithmetic.ProductMap

namespace JonnyLean.Arithmetic

theorem product_map_mono (f g : α → Nat) (xs : List α)
    (h : ∀ a ∈ xs, f a ≤ g a) : product (xs.map f) ≤ product (xs.map g) := by
  induction xs with
  | nil => exact Nat.le_refl 1
  | cons a xs ih =>
    exact Nat.mul_le_mul (h a (by simp)) (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem product_bound (c : Nat) (xs : List Nat) (h : ∀ a ∈ xs, a ≤ c) :
    product xs ≤ c^xs.length := by
  have hp := product_map_mono id (fun _ => c) xs h
  simpa [product_map_const] using hp

theorem product_lower_bound (c : Nat) (xs : List Nat) (h : ∀ a ∈ xs, c ≤ a) :
    c^xs.length ≤ product xs := by
  have hp := product_map_mono (fun _ => c) id xs h
  simpa [product_map_const] using hp

theorem product_reverse (xs : List Nat) : product xs.reverse = product xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.reverse_cons, product_append, product, ih, Nat.mul_comm]

theorem product_split (n : Nat) (xs : List Nat) :
    product xs = product (xs.take n) * product (xs.drop n) := by
  rw [← product_append, List.take_append_drop]

end JonnyLean.Arithmetic
