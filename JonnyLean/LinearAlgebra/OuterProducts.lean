import JonnyLean.LinearAlgebra.DiagonalTrace

namespace JonnyLean.LinearAlgebra

/-- Rank-one style construction over the natural-number semiring. -/
def outer (x : Vec m) (y : Vec n) : Mat m n := fun i j => x i * y j

theorem outer_action (x : Vec m) (y z : Vec n) : act (outer x y) z = scale (dot y z) x := by
  funext i
  simp only [act, dot, outer, Nat.mul_assoc, sum_mul_left, scale]
  exact Nat.mul_comm _ _

theorem outer_mul (x : Vec m) (y z : Vec n) (w : Vec p) :
    mulMat (outer x y) (outer z w) = scaleMat (dot y z) (outer x w) := by
  funext i j
  change sum (fun k => (x i * y k) * (z k * w j)) = dot y z * (x i * w j)
  calc
    _ = sum (fun k => (x i * w j) * (y k * z k)) := by
      apply sum_congr; intro k
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    _ = (x i * w j) * dot y z := sum_mul_left _ _
    _ = _ := Nat.mul_comm _ _

theorem transpose_outer (x : Vec m) (y : Vec n) : transpose (outer x y) = outer y x := by
  funext i j; exact Nat.mul_comm _ _

theorem outer_trace (x y : Vec n) : trace (outer x y) = dot x y := rfl

theorem outer_add_left (x y : Vec m) (z : Vec n) : outer (vadd x y) z = addMat (outer x z) (outer y z) := by
  funext i j; exact Nat.add_mul _ _ _
theorem outer_add_right (x : Vec m) (y z : Vec n) : outer x (vadd y z) = addMat (outer x y) (outer x z) := by
  funext i j; exact Nat.mul_add _ _ _
theorem outer_scale_left (a : Nat) (x : Vec m) (y : Vec n) : outer (scale a x) y = scaleMat a (outer x y) := by
  funext i j; exact Nat.mul_assoc _ _ _
theorem outer_self_trace_zero (x : Vec n) : trace (outer x x) = 0 ↔ x = vzero :=
  dot_self_zero_iff x

theorem matrix_outer_basis (A : Mat m n) :
    (fun i j => sum (fun k => A i k * basis k j)) = A := by
  funext i j; exact sum_delta_right j (A i)

/-- A normalized outer product is an idempotent endomorphism. -/
theorem outer_idempotent_of_dot_one (x y : Vec n) (h : dot y x = 1) :
    mulMat (outer x y) (outer x y) = outer x y := by
  rw [outer_mul, h, scaleMat_one]

theorem outer_action_idempotent (x y z : Vec n) (h : dot y x = 1) :
    act (outer x y) (act (outer x y) z) = act (outer x y) z := by
  rw [← act_comp, outer_idempotent_of_dot_one x y h]

theorem outer_normalized_trace (x y : Vec n) (h : dot y x = 1) :
    trace (outer x y) = 1 := by
  rw [outer_trace, dot_symm, h]

end JonnyLean.LinearAlgebra
