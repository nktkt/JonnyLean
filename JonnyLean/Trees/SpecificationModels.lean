import JonnyLean.Trees.Binary

/-! Fixed independent mathematical models and checked bridges for the task contracts. -/

namespace JonnyLean.VerifiedPrograms.Specification

open Trees

def traversal : Tree α → List α
  | .empty => []
  | .node l x r => traversal l ++ [x] ++ traversal r

def nodes : Tree α → Nat
  | .empty => 0
  | .node l _ r => 1 + nodes l + nodes r

def levels : Tree α → Nat
  | .empty => 0
  | .node l _ r => 1 + max (levels l) (levels r)

def leaves : Tree α → Nat
  | .empty => 1
  | .node l _ r => leaves l + leaves r

def treePredicate (p : α → Prop) : Tree α → Prop
  | .empty => True
  | .node l x r => p x ∧ treePredicate p l ∧ treePredicate p r

def treeFold (z : β) (combine : β → α → β → β) : Tree α → β
  | .empty => z
  | .node l x r => combine (treeFold z combine l) x (treeFold z combine r)

theorem traversal_matches (t : Tree α) : traversal t = Tree.inorder t := by
  induction t <;> simp_all [traversal, Tree.inorder, List.append_assoc]

theorem nodes_matches (t : Tree α) : nodes t = Tree.size t := by
  induction t with
  | empty => rfl
  | node l x r hl hr => simp only [nodes, Tree.size, hl, hr]; omega

theorem levels_matches (t : Tree α) : levels t = Tree.height t := by
  induction t with
  | empty => rfl
  | node l x r hl hr => simp only [levels, Tree.height, hl, hr]; omega

theorem leaves_matches (t : Tree α) : leaves t = Tree.externalLeaves t := by
  induction t <;> simp_all [leaves, Tree.externalLeaves]

theorem treePredicate_matches (p : α → Prop) (t : Tree α) : treePredicate p t ↔ Tree.All p t := by
  induction t <;> simp_all [treePredicate, Tree.All, and_left_comm]

theorem treeFold_matches (z : β) (combine : β → α → β → β) (t : Tree α) :
    treeFold z combine t = Tree.fold z combine t := by
  induction t <;> simp_all [treeFold, Tree.fold]

end JonnyLean.VerifiedPrograms.Specification
