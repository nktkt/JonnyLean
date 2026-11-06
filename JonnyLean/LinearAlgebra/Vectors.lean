import JonnyLean.LinearAlgebra.FiniteSums

namespace JonnyLean.LinearAlgebra

abbrev Vec (n : Nat) := Fin n → Nat

def vzero : Vec n := fun _ => 0
def vadd (x y : Vec n) : Vec n := fun i => x i + y i
def scale (a : Nat) (x : Vec n) : Vec n := fun i => a * x i
def basis (i : Fin n) : Vec n := delta i
def dot (x y : Vec n) : Nat := sum (fun i => x i * y i)
def VecLE (x y : Vec n) : Prop := ∀ i, x i ≤ y i

theorem vadd_assoc (x y z : Vec n) : vadd (vadd x y) z = vadd x (vadd y z) := by
  funext i; exact Nat.add_assoc _ _ _
theorem vadd_comm (x y : Vec n) : vadd x y = vadd y x := by
  funext i; exact Nat.add_comm _ _
theorem vadd_zero (x : Vec n) : vadd x vzero = x := by
  funext i; exact Nat.add_zero _
theorem scale_add (a : Nat) (x y : Vec n) : scale a (vadd x y) = vadd (scale a x) (scale a y) := by
  funext i; exact Nat.mul_add _ _ _
theorem scale_scale (a b : Nat) (x : Vec n) : scale a (scale b x) = scale (a*b) x := by
  funext i; exact (Nat.mul_assoc _ _ _).symm

theorem dot_symm (x y : Vec n) : dot x y = dot y x := by
  apply sum_congr; intro i; exact Nat.mul_comm _ _
theorem dot_zero (x : Vec n) : dot x vzero = 0 := by simp [dot, vzero, sum_zero]
theorem dot_add_left (x y z : Vec n) : dot (vadd x y) z = dot x z + dot y z := by
  simp only [dot, vadd, Nat.add_mul, sum_add]
theorem dot_add_right (x y z : Vec n) : dot x (vadd y z) = dot x y + dot x z := by
  simp only [dot, vadd, Nat.mul_add, sum_add]
theorem dot_scale_left (a : Nat) (x y : Vec n) : dot (scale a x) y = a * dot x y := by
  simp only [dot, scale, Nat.mul_assoc, sum_mul_left]
theorem dot_scale_right (a : Nat) (x y : Vec n) : dot x (scale a y) = a * dot x y := by
  rw [dot_symm, dot_scale_left, dot_symm]

theorem dot_bilinear (a b : Nat) (u v x y : Vec n) :
    dot (vadd (scale a u) v) (vadd (scale b x) y) =
      a*b*dot u x + a*dot u y + b*dot v x + dot v y := by
  simp only [dot_add_left, dot_add_right, dot_scale_left, dot_scale_right]
  simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm]; omega

theorem dot_self_zero_iff (x : Vec n) : dot x x = 0 ↔ x = vzero := by
  rw [dot, sum_eq_zero_iff]
  constructor
  · intro h; funext i
    have hi := h i
    simpa [vzero, Nat.mul_eq_zero] using hi
  · intro h; subst x; intro i; rfl

theorem dot_mono (x x' y y' : Vec n) (hx : VecLE x x') (hy : VecLE y y') :
    dot x y ≤ dot x' y' := by
  exact sum_mono _ _ (fun i => Nat.mul_le_mul (hx i) (hy i))

theorem dot_bound (x y : Vec n) (a b : Nat) (hx : ∀ i, x i ≤ a) (hy : ∀ i, y i ≤ b) :
    dot x y ≤ n * (a*b) := by
  rw [← sum_constant]
  exact sum_mono _ _ (fun i => Nat.mul_le_mul (hx i) (hy i))

theorem dot_basis (x : Vec n) (j : Fin n) : dot x (basis j) = x j := by
  simpa only [dot, basis, delta_symm] using sum_delta_right j x

theorem basis_reconstruction (x : Vec n) :
    (fun j => sum (fun i => x i * basis i j)) = x := by
  funext j; exact sum_delta_right j x

theorem vectors_equal_of_basis (x y : Vec n) (h : ∀ i, dot x (basis i) = dot y (basis i)) :
    x = y := by
  funext i; simpa only [dot_basis] using h i

theorem dot_zero_iff (x y : Vec n) : dot x y = 0 ↔ ∀ i, x i = 0 ∨ y i = 0 := by
  simp only [dot, sum_eq_zero_iff, Nat.mul_eq_zero]

end JonnyLean.LinearAlgebra
