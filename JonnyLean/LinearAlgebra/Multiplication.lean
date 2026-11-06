import JonnyLean.LinearAlgebra.Matrices

namespace JonnyLean.LinearAlgebra

/-- Rectangular multiplication sums over the shared dimension only. -/
def mulMat (A : Mat m n) (B : Mat n p) : Mat m p :=
  fun i k => sum (fun j => A i j * B j k)

theorem mulMat_add_right (A : Mat m n) (B C : Mat n p) :
    mulMat A (addMat B C) = addMat (mulMat A B) (mulMat A C) := by
  funext i k; simp only [mulMat, addMat, Nat.mul_add, sum_add]
theorem mulMat_add_left (A B : Mat m n) (C : Mat n p) :
    mulMat (addMat A B) C = addMat (mulMat A C) (mulMat B C) := by
  funext i k; simp only [mulMat, addMat, Nat.add_mul, sum_add]

theorem mulMat_assoc (A : Mat m n) (B : Mat n p) (C : Mat p q) :
    mulMat (mulMat A B) C = mulMat A (mulMat B C) := by
  funext i l
  simp only [mulMat, ← sum_mul_right, ← sum_mul_left]
  rw [sum_swap]
  apply sum_congr; intro j
  apply sum_congr; intro k
  exact Nat.mul_assoc _ _ _

theorem identity_mulMat (A : Mat m n) : mulMat (identity m) A = A := by
  funext i j; exact sum_delta i (fun k => A k j)
theorem mulMat_identity (A : Mat m n) : mulMat A (identity n) = A := by
  funext i j; exact sum_delta_right j (A i)
theorem mulMat_identities (A : Mat m n) :
    mulMat (identity m) A = A ∧ mulMat A (identity n) = A :=
  ⟨identity_mulMat A, mulMat_identity A⟩

theorem transpose_mulMat (A : Mat m n) (B : Mat n p) :
    transpose (mulMat A B) = mulMat (transpose B) (transpose A) := by
  funext i j
  apply sum_congr; intro k
  exact Nat.mul_comm _ _

theorem mulMat_scale_left (a : Nat) (A : Mat m n) (B : Mat n p) :
    mulMat (scaleMat a A) B = scaleMat a (mulMat A B) := by
  funext i j; simp only [mulMat, scaleMat, Nat.mul_assoc, sum_mul_left]
theorem mulMat_scale_right (a : Nat) (A : Mat m n) (B : Mat n p) :
    mulMat A (scaleMat a B) = scaleMat a (mulMat A B) := by
  funext i j
  simp only [mulMat, scaleMat, Nat.mul_left_comm, sum_mul_left]
theorem mulMat_scaled (a b : Nat) (A : Mat m n) (B : Mat n p) :
    mulMat (scaleMat a A) (scaleMat b B) = scaleMat (a*b) (mulMat A B) := by
  rw [mulMat_scale_left, mulMat_scale_right, scaleMat_comp]

theorem mulMat_zero_right (A : Mat m n) : mulMat A (zeroMat : Mat n p) = zeroMat := by
  funext i j; simp [mulMat, zeroMat, sum_zero]
theorem mulMat_zero_left (A : Mat n p) : mulMat (zeroMat : Mat m n) A = zeroMat := by
  funext i j; simp [mulMat, zeroMat, sum_zero]
theorem mulMat_zeros (A : Mat m n) (B : Mat n p) :
    mulMat A (zeroMat : Mat n p) = zeroMat ∧ mulMat (zeroMat : Mat m n) B = zeroMat :=
  ⟨mulMat_zero_right A, mulMat_zero_left B⟩

theorem mulMat_mono (A A' : Mat m n) (B B' : Mat n p)
    (hA : MatLE A A') (hB : MatLE B B') : MatLE (mulMat A B) (mulMat A' B') := by
  intro i k
  exact sum_mono _ _ (fun j => Nat.mul_le_mul (hA i j) (hB j k))

theorem mulMat_bound (A : Mat m n) (B : Mat n p) (a b : Nat)
    (hA : ∀ i j, A i j ≤ a) (hB : ∀ j k, B j k ≤ b) :
    ∀ i k, mulMat A B i k ≤ n * (a*b) := by
  intro i k
  rw [← sum_constant]
  exact sum_mono _ _ (fun j => Nat.mul_le_mul (hA i j) (hB j k))

end JonnyLean.LinearAlgebra
