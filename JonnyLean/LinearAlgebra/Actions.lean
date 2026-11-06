import JonnyLean.LinearAlgebra.Multiplication

namespace JonnyLean.LinearAlgebra

/-- Matrix action on a column vector. -/
def act (A : Mat m n) (x : Vec n) : Vec m := fun i => dot (A i) x

theorem act_comp (A : Mat m n) (B : Mat n p) (x : Vec p) :
    act (mulMat A B) x = act A (act B x) := by
  funext i
  simp only [act, dot, mulMat, ← sum_mul_right, ← sum_mul_left]
  rw [sum_swap]
  apply sum_congr; intro j
  apply sum_congr; intro k
  exact Nat.mul_assoc _ _ _

theorem act_add (A : Mat m n) (x y : Vec n) : act A (vadd x y) = vadd (act A x) (act A y) := by
  funext i; exact dot_add_right (A i) x y
theorem act_scale (A : Mat m n) (a : Nat) (x : Vec n) : act A (scale a x) = scale a (act A x) := by
  funext i; exact dot_scale_right a (A i) x
theorem act_linear (A : Mat m n) (a b : Nat) (x y : Vec n) :
    act A (vadd (scale a x) (scale b y)) = vadd (scale a (act A x)) (scale b (act A y)) := by
  rw [act_add, act_scale, act_scale]
theorem act_matrix_add (A B : Mat m n) (x : Vec n) :
    act (addMat A B) x = vadd (act A x) (act B x) := by
  funext i; exact dot_add_left (A i) (B i) x
theorem act_zero (A : Mat m n) : act A vzero = vzero := by
  funext i; exact dot_zero (A i)
theorem zero_act (x : Vec n) : act (zeroMat : Mat m n) x = vzero := by
  funext i; simp [act, dot, zeroMat, vzero, sum_zero]
theorem identity_act (x : Vec n) : act (identity n) x = x := by
  funext i; exact sum_delta i x

theorem act_basis (A : Mat m n) (j : Fin n) : act A (basis j) = fun i => A i j := by
  funext i; exact dot_basis (A i) j

theorem matrix_eq_of_basis_actions (A B : Mat m n)
    (h : ∀ j, act A (basis j) = act B (basis j)) : A = B := by
  funext i j
  have hi := congrFun (h j) i
  simpa only [act_basis] using hi

theorem act_mono (A B : Mat m n) (x y : Vec n) (hA : MatLE A B) (hx : VecLE x y) :
    VecLE (act A x) (act B y) := by
  intro i; exact dot_mono (A i) (B i) x y (hA i) hx

end JonnyLean.LinearAlgebra
