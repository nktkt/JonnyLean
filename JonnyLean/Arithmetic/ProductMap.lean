import JonnyLean.Arithmetic.Product

namespace JonnyLean.Arithmetic

theorem product_map_mul (f g : α → Nat) (xs : List α) :
    product (xs.map (fun a => f a*g a)) = product (xs.map f)*product (xs.map g) := by
  induction xs with
  | nil => simp [product]
  | cons a xs ih =>
    simp only [List.map_cons, product, ih]
    ac_rfl

theorem product_map_const (a : Nat) (xs : List α) :
    product (xs.map (fun _ => a)) = a^xs.length := by
  induction xs with
  | nil => simp [product]
  | cons b xs ih => simp [product, ih, Nat.pow_succ, Nat.mul_comm]

theorem product_map_pow (n : Nat) (xs : List Nat) :
    product (xs.map (fun a => a^n)) = (product xs)^n := by
  induction xs with
  | nil => simp [product]
  | cons a xs ih => simp [product, ih, Nat.mul_pow]

theorem product_map_scale (c : Nat) (xs : List Nat) :
    product (xs.map (fun a => c*a)) = c^xs.length * product xs := by
  rw [product_map_mul, product_map_const]
  simp

end JonnyLean.Arithmetic
