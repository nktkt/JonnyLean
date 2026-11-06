import JonnyLean.LinearAlgebra.Actions

namespace JonnyLean.LinearAlgebra

/-- Diagonal matrix, with each off-diagonal entry explicitly zero. -/
def diagonal (d : Vec n) : Mat n n := fun i j => d i * delta i j
def trace (A : Mat n n) : Nat := sum (fun i => A i i)
def hadamard (x y : Vec n) : Vec n := fun i => x i * y i

theorem diagonal_entry (d : Vec n) (i : Fin n) : diagonal d i i = d i := by
  simp [diagonal, delta]
theorem diagonal_off (d : Vec n) (i j : Fin n) (h : i ≠ j) : diagonal d i j = 0 := by
  simp [diagonal, delta, h]
theorem diagonal_one (n : Nat) : diagonal (fun _ : Fin n => 1) = identity n := by
  funext i j; exact Nat.one_mul _
theorem diagonal_zero (n : Nat) : diagonal (vzero : Vec n) = zeroMat := by
  funext i j; exact Nat.zero_mul _
theorem diagonal_add (d e : Vec n) : diagonal (vadd d e) = addMat (diagonal d) (diagonal e) := by
  funext i j; exact Nat.add_mul _ _ _
theorem transpose_diagonal (d : Vec n) : transpose (diagonal d) = diagonal d := by
  funext i j
  by_cases h : i = j
  · subst j; rfl
  · simp [transpose, diagonal, delta, h, Ne.symm h]

theorem diagonal_mul_left (d : Vec m) (A : Mat m n) :
    mulMat (diagonal d) A = fun i j => d i * A i j := by
  funext i j
  simp only [mulMat, diagonal, Nat.mul_assoc, sum_mul_left]
  rw [sum_delta]
theorem diagonal_mul_right (A : Mat m n) (d : Vec n) :
    mulMat A (diagonal d) = fun i j => A i j * d j := by
  funext i j
  simpa only [mulMat, diagonal, ← Nat.mul_assoc] using sum_delta_right j (fun k => A i k * d k)

theorem diagonal_mul (d e : Vec n) :
    mulMat (diagonal d) (diagonal e) = diagonal (hadamard d e) := by
  rw [diagonal_mul_left]
  funext i j; exact (Nat.mul_assoc _ _ _).symm

theorem diagonal_act (d x : Vec n) : act (diagonal d) x = hadamard d x := by
  funext i
  simp only [act, dot, diagonal, Nat.mul_assoc, sum_mul_left]
  exact congrArg (fun a => d i * a) (sum_delta i x)

theorem trace_add (A B : Mat n n) : trace (addMat A B) = trace A + trace B := by
  exact sum_add _ _
theorem trace_scale (a : Nat) (A : Mat n n) : trace (scaleMat a A) = a * trace A := by
  exact sum_mul_left a _
theorem trace_linear (a b : Nat) (A B : Mat n n) :
    trace (addMat (scaleMat a A) (scaleMat b B)) = a * trace A + b * trace B := by
  rw [trace_add, trace_scale, trace_scale]
theorem trace_transpose (A : Mat n n) : trace (transpose A) = trace A := rfl
theorem trace_diagonal (d : Vec n) : trace (diagonal d) = sum d := by
  apply sum_congr; intro i; exact diagonal_entry d i
theorem trace_identity (n : Nat) : trace (identity n) = n := by
  simp [trace, identity, delta, sum_constant]

theorem trace_mul_cyclic (A : Mat m n) (B : Mat n m) : trace (mulMat A B) = trace (mulMat B A) := by
  unfold trace mulMat
  rw [sum_swap]
  apply sum_congr; intro i
  apply sum_congr; intro j
  exact Nat.mul_comm _ _

end JonnyLean.LinearAlgebra
