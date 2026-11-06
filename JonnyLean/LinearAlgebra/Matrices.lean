import JonnyLean.LinearAlgebra.Vectors

namespace JonnyLean.LinearAlgebra

/-- A rectangular natural-number matrix with dimensions in its type. -/
abbrev Mat (m n : Nat) := Fin m → Fin n → Nat

def zeroMat : Mat m n := fun _ _ => 0
def addMat (A B : Mat m n) : Mat m n := fun i j => A i j + B i j
def scaleMat (a : Nat) (A : Mat m n) : Mat m n := fun i j => a * A i j
def transpose (A : Mat m n) : Mat n m := fun i j => A j i
def identity (n : Nat) : Mat n n := delta
def MatLE (A B : Mat m n) : Prop := ∀ i j, A i j ≤ B i j

theorem addMat_assoc (A B C : Mat m n) : addMat (addMat A B) C = addMat A (addMat B C) := by
  funext i j; exact Nat.add_assoc _ _ _
theorem addMat_comm (A B : Mat m n) : addMat A B = addMat B A := by
  funext i j; exact Nat.add_comm _ _
theorem addMat_zero (A : Mat m n) : addMat A zeroMat = A := by
  funext i j; exact Nat.add_zero _
theorem scaleMat_add (a : Nat) (A B : Mat m n) :
    scaleMat a (addMat A B) = addMat (scaleMat a A) (scaleMat a B) := by
  funext i j; exact Nat.mul_add _ _ _
theorem scaleMat_sum (a b : Nat) (A : Mat m n) :
    scaleMat (a+b) A = addMat (scaleMat a A) (scaleMat b A) := by
  funext i j; exact Nat.add_mul _ _ _
theorem scaleMat_comp (a b : Nat) (A : Mat m n) :
    scaleMat a (scaleMat b A) = scaleMat (a*b) A := by
  funext i j; exact (Nat.mul_assoc _ _ _).symm
theorem scaleMat_one (A : Mat m n) : scaleMat 1 A = A := by
  funext i j; exact Nat.one_mul _

theorem transpose_transpose (A : Mat m n) : transpose (transpose A) = A := rfl
theorem transpose_add (A B : Mat m n) :
    transpose (addMat A B) = addMat (transpose A) (transpose B) := rfl
theorem transpose_scale (a : Nat) (A : Mat m n) :
    transpose (scaleMat a A) = scaleMat a (transpose A) := rfl
theorem transpose_identity (n : Nat) : transpose (identity n) = identity n := by
  funext i j; exact delta_symm j i

theorem matrix_semimodule_laws (a b : Nat) (A B : Mat m n) :
    scaleMat a (addMat A B) = addMat (scaleMat a A) (scaleMat a B) ∧
    scaleMat (a+b) A = addMat (scaleMat a A) (scaleMat b A) ∧
    scaleMat a (scaleMat b A) = scaleMat (a*b) A ∧ scaleMat 1 A = A :=
  ⟨scaleMat_add a A B, scaleMat_sum a b A, scaleMat_comp a b A, scaleMat_one A⟩

end JonnyLean.LinearAlgebra
