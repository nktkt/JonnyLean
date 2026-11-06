import JonnyLean.LinearAlgebra.DiagonalTrace

namespace JonnyLean.LinearAlgebra

/-- Four typed quadrants; vectors are pairs, without flattening their indices. -/
structure Block (m n p q : Nat) where
  tl : Mat m p
  tr : Mat m q
  bl : Mat n p
  br : Mat n q

def blockAct (A : Block m n p q) (x : Vec p × Vec q) : Vec m × Vec n :=
  (vadd (act A.tl x.1) (act A.tr x.2), vadd (act A.bl x.1) (act A.br x.2))

def blockMul (A : Block m n p q) (B : Block p q r s) : Block m n r s :=
  ⟨addMat (mulMat A.tl B.tl) (mulMat A.tr B.bl),
   addMat (mulMat A.tl B.tr) (mulMat A.tr B.br),
   addMat (mulMat A.bl B.tl) (mulMat A.br B.bl),
   addMat (mulMat A.bl B.tr) (mulMat A.br B.br)⟩

def blockTranspose (A : Block m n p q) : Block p q m n :=
  ⟨transpose A.tl, transpose A.bl, transpose A.tr, transpose A.br⟩

def blockDiagonal (A : Mat m p) (B : Mat n q) : Block m n p q :=
  ⟨A, zeroMat, zeroMat, B⟩

def pairAdd (x y : Vec m × Vec n) : Vec m × Vec n := (vadd x.1 y.1, vadd x.2 y.2)
def pairScale (a : Nat) (x : Vec m × Vec n) : Vec m × Vec n := (scale a x.1, scale a x.2)

theorem blockAct_comp (A : Block m n p q) (B : Block p q r s) (x : Vec r × Vec s) :
    blockAct (blockMul A B) x = blockAct A (blockAct B x) := by
  apply Prod.ext
  · simp only [blockAct, blockMul, act_matrix_add, act_comp, act_add]
    funext i; simp only [vadd]; omega
  · simp only [blockAct, blockMul, act_matrix_add, act_comp, act_add]
    funext i; simp only [vadd]; omega

theorem blockAct_add (A : Block m n p q) (x y : Vec p × Vec q) :
    blockAct A (pairAdd x y) = pairAdd (blockAct A x) (blockAct A y) := by
  apply Prod.ext
  · simp only [blockAct, pairAdd, act_add]
    funext i; simp only [vadd]; omega
  · simp only [blockAct, pairAdd, act_add]
    funext i; simp only [vadd]; omega

theorem blockAct_scale (A : Block m n p q) (a : Nat) (x : Vec p × Vec q) :
    blockAct A (pairScale a x) = pairScale a (blockAct A x) := by
  apply Prod.ext
  · simp only [blockAct, pairScale, act_scale, scale_add]
  · simp only [blockAct, pairScale, act_scale, scale_add]

theorem blockAct_linear (A : Block m n p q) (a b : Nat) (x y : Vec p × Vec q) :
    blockAct A (pairAdd (pairScale a x) (pairScale b y)) =
      pairAdd (pairScale a (blockAct A x)) (pairScale b (blockAct A y)) := by
  rw [blockAct_add, blockAct_scale, blockAct_scale]

theorem blockDiagonal_act (A : Mat m p) (B : Mat n q) (x : Vec p × Vec q) :
    blockAct (blockDiagonal A B) x = (act A x.1, act B x.2) := by
  simp only [blockAct, blockDiagonal, zero_act, vadd_zero]
  apply Prod.ext
  · rfl
  · funext i; exact Nat.zero_add _

theorem blockDiagonal_mul (A : Mat m p) (B : Mat n q) (C : Mat p r) (D : Mat q s) :
    blockMul (blockDiagonal A B) (blockDiagonal C D) =
      blockDiagonal (mulMat A C) (mulMat B D) := by
  simp only [blockMul, blockDiagonal, mulMat_zero_left, mulMat_zero_right, addMat_zero]
  congr 1
  funext i j; exact Nat.zero_add _

theorem blockTranspose_involution (A : Block m n p q) : blockTranspose (blockTranspose A) = A := by
  cases A; rfl

theorem blockTranspose_mul (A : Block m n p q) (B : Block p q r s) :
    blockTranspose (blockMul A B) = blockMul (blockTranspose B) (blockTranspose A) := by
  simp only [blockTranspose, blockMul, transpose_add, transpose_mulMat]

theorem blockDiagonal_transpose (A : Mat m p) (B : Mat n q) :
    blockTranspose (blockDiagonal A B) = blockDiagonal (transpose A) (transpose B) := rfl

end JonnyLean.LinearAlgebra
