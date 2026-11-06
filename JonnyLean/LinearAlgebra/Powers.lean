import JonnyLean.LinearAlgebra.DiagonalTrace

namespace JonnyLean.LinearAlgebra

def matPow (A : Mat n n) : Nat → Mat n n
  | 0 => identity n
  | k + 1 => mulMat A (matPow A k)

def iterateAct (A : Mat n n) : Nat → Vec n → Vec n
  | 0, x => x
  | k + 1, x => act A (iterateAct A k x)

theorem matPow_zero (A : Mat n n) : matPow A 0 = identity n := rfl
theorem matPow_succ (A : Mat n n) (k : Nat) : matPow A (k+1) = mulMat A (matPow A k) := rfl
theorem matPow_one (A : Mat n n) : matPow A 1 = A := mulMat_identity A

theorem matPow_add (A : Mat n n) (k l : Nat) :
    matPow A (k+l) = mulMat (matPow A k) (matPow A l) := by
  induction k with
  | zero => simp [matPow, identity_mulMat]
  | succ k ih =>
    rw [Nat.succ_add, matPow_succ, ih, matPow_succ, mulMat_assoc]

theorem matPow_factors_commute (A : Mat n n) (k l : Nat) :
    mulMat (matPow A k) (matPow A l) = mulMat (matPow A l) (matPow A k) := by
  rw [← matPow_add, ← matPow_add, Nat.add_comm]

theorem matPow_succ_right (A : Mat n n) (k : Nat) :
    matPow A (k+1) = mulMat (matPow A k) A := by
  rw [matPow_add, matPow_one]

theorem matPow_action (A : Mat n n) (k : Nat) (x : Vec n) :
    act (matPow A k) x = iterateAct A k x := by
  induction k with
  | zero => exact identity_act x
  | succ k ih => simp only [matPow, act_comp, iterateAct, ih]

theorem matPow_diagonal (d : Vec n) (k : Nat) :
    matPow (diagonal d) k = diagonal (fun i => d i ^ k) := by
  induction k with
  | zero => simp only [matPow, Nat.pow_zero, diagonal_one]
  | succ k ih =>
    rw [matPow_succ, ih, diagonal_mul]
    congr 1; funext i
    simp only [hadamard, Nat.pow_succ, Nat.mul_comm]

theorem matPow_transpose (A : Mat n n) (k : Nat) :
    transpose (matPow A k) = matPow (transpose A) k := by
  induction k with
  | zero => exact transpose_identity n
  | succ k ih => rw [matPow_succ, transpose_mulMat, ih, ← matPow_succ_right]

theorem matPow_identity (n k : Nat) : matPow (identity n) k = identity n := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [matPow, identity_mulMat, ih]

end JonnyLean.LinearAlgebra
