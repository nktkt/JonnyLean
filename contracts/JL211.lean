import JonnyLean.LinearAlgebra.Blocks

open JonnyLean.LinearAlgebra

/-- Independent expected type, with finite index domains explicit. -/
theorem contract_JL211 {m n p q r s : Nat} (A : Fin m → Fin p → Nat) (B : Fin n → Fin q → Nat) (C : Fin p → Fin r → Nat) (D : Fin q → Fin s → Nat) :
    blockMul (blockDiagonal A B) (blockDiagonal C D) = blockDiagonal (mulMat A C) (mulMat B D) :=
  blockDiagonal_mul A B C D

theorem contract_JL211_definition {m n p q : Nat} (A : Block m n p q) (x : (Fin p → Nat) × (Fin q → Nat)) :
    (blockAct A x).1 = (fun i => sum (fun j => A.tl i j * x.1 j) + sum (fun j => A.tr i j * x.2 j)) := rfl

theorem contract_JL211_concrete : (blockAct (Block.mk (fun _ _ => 1) (fun _ _ => 2) (fun _ _ => 3) (fun _ _ => 4) : Block 1 1 1 1) ((fun _ => 5),(fun _ => 6))).2 0 = 39 := by decide

theorem contract_JL211_boundary : (blockMul (blockDiagonal (identity 1) (identity 1)) (blockDiagonal (identity 1) (identity 1))).tr 0 0 = 0 := by decide

#print axioms JonnyLean.LinearAlgebra.blockDiagonal_mul
#print axioms contract_JL211
