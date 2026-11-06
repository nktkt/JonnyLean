import Std

namespace JonnyLean.Trees

inductive Tree (α : Type u) where
  | empty
  | node (left : Tree α) (value : α) (right : Tree α)
  deriving Repr, DecidableEq

namespace Tree

def size : Tree α → Nat
  | .empty => 0
  | .node l _ r => size l + size r + 1

def height : Tree α → Nat
  | .empty => 0
  | .node l _ r => max (height l) (height r) + 1

def inorder : Tree α → List α
  | .empty => []
  | .node l x r => inorder l ++ x :: inorder r

def mirror : Tree α → Tree α
  | .empty => .empty
  | .node l x r => .node (mirror r) x (mirror l)

def map (f : α → β) : Tree α → Tree β
  | .empty => .empty
  | .node l x r => .node (map f l) (f x) (map f r)

def fold (z : β) (step : β → α → β → β) : Tree α → β
  | .empty => z
  | .node l x r => step (fold z step l) x (fold z step r)

def graft (replacement : Tree α) : Tree α → Tree α
  | .empty => replacement
  | .node l x r => .node (graft replacement l) x (graft replacement r)

def prune : Nat → Tree α → Tree α
  | 0, _ => .empty
  | _ + 1, .empty => .empty
  | n + 1, .node l x r => .node (prune n l) x (prune n r)

def All (p : α → Prop) : Tree α → Prop
  | .empty => True
  | .node l x r => All p l ∧ p x ∧ All p r

def inorderInto : Tree α → List α → List α
  | .empty, acc => acc
  | .node l x r, acc => inorderInto l (x :: inorderInto r acc)

def externalLeaves : Tree α → Nat
  | .empty => 1
  | .node l _ r => externalLeaves l + externalLeaves r

theorem inorder_length (t : Tree α) : (inorder t).length = size t := by
  induction t with
  | empty => rfl
  | node l x r hl hr => simp only [inorder, size, List.length_append, List.length_cons, hl, hr]; omega

theorem inorder_mirror (t : Tree α) : inorder (mirror t) = (inorder t).reverse := by
  induction t with
  | empty => rfl
  | node l x r hl hr => simp [mirror, inorder, hl, hr, List.reverse_append, List.append_assoc]

theorem mirror_involution (t : Tree α) : mirror (mirror t) = t := by
  induction t with
  | empty => rfl
  | node l x r hl hr => simp [mirror, hl, hr]

theorem mirror_size (t : Tree α) : size (mirror t) = size t := by
  induction t with
  | empty => rfl
  | node l x r hl hr => simp [mirror, size, hl, hr, Nat.add_comm]

theorem inorder_map (f : α → β) (t : Tree α) :
    inorder (map f t) = (inorder t).map f := by
  induction t with
  | empty => rfl
  | node l x r hl hr => simp [map, inorder, hl, hr]

theorem map_comp (f : α → β) (g : β → γ) (t : Tree α) :
    map g (map f t) = map (g ∘ f) t := by
  induction t with
  | empty => rfl
  | node l x r hl hr => simp [map, hl, hr]

theorem map_size (f : α → β) (t : Tree α) : size (map f t) = size t := by
  induction t with
  | empty => rfl
  | node l x r hl hr => simp [map, size, hl, hr]

theorem height_le_size (t : Tree α) : height t ≤ size t := by
  induction t with
  | empty => exact Nat.le_refl _
  | node l x r hl hr => simp only [height, size]; omega

theorem fold_fusion (f : β → γ) (z : β) (step : β → α → β → β)
    (step' : γ → α → γ → γ)
    (h : ∀ a x b, f (step a x b) = step' (f a) x (f b)) (t : Tree α) :
    f (fold z step t) = fold (f z) step' t := by
  induction t with
  | empty => rfl
  | node l x r hl hr => simp only [fold, h, hl, hr]

theorem fold_size (t : Tree α) : fold 0 (fun l _ r => l + r + 1) t = size t := by
  induction t with
  | empty => rfl
  | node l x r hl hr => simp only [fold, size, hl, hr]

theorem graft_size (s t : Tree α) :
    size (graft s t) = size t + (size t + 1) * size s := by
  induction t with
  | empty => simp [graft, size]
  | node l x r hl hr =>
    simp only [graft, size, hl, hr, Nat.add_mul, Nat.one_mul]
    omega

theorem graft_empty (t : Tree α) : graft .empty t = t := by
  induction t with
  | empty => rfl
  | node l x r hl hr => simp [graft, hl, hr]

theorem graft_assoc (s t u : Tree α) : graft s (graft t u) = graft (graft s t) u := by
  induction u with
  | empty => rfl
  | node l x r hl hr => simp only [graft, hl, hr]

theorem prune_height (n : Nat) (t : Tree α) : height (prune n t) ≤ n := by
  induction n generalizing t with
  | zero => simp [prune, height]
  | succ n ih =>
    cases t with
    | empty => simp [prune, height]
    | node l x r => simp only [prune, height]; have := ih l; have := ih r; omega

theorem prune_of_height_le (n : Nat) (t : Tree α) (h : height t ≤ n) : prune n t = t := by
  induction n generalizing t with
  | zero =>
    cases t with
    | empty => rfl
    | node l x r =>
      simp only [height] at h
      exact False.elim (by omega)
  | succ n ih =>
    cases t with
    | empty => rfl
    | node l x r =>
      simp only [height] at h
      have hl : height l ≤ n := by omega
      have hr : height r ≤ n := by omega
      simp only [prune, ih l hl, ih r hr]

theorem prune_idempotent (n : Nat) (t : Tree α) : prune n (prune n t) = prune n t :=
  prune_of_height_le n _ (prune_height n t)

theorem all_iff_inorder (p : α → Prop) (t : Tree α) :
    All p t ↔ ∀ x ∈ inorder t, p x := by
  induction t with
  | empty => simp [All, inorder]
  | node l x r hl hr => simp [All, inorder, hl, hr, or_imp, forall_and]

theorem all_map (p : β → Prop) (f : α → β) (t : Tree α) :
    All p (map f t) ↔ All (p ∘ f) t := by
  induction t with
  | empty => rfl
  | node l x r hl hr => simp [map, All, hl, hr]

theorem inorderInto_spec (t : Tree α) (acc : List α) :
    inorderInto t acc = inorder t ++ acc := by
  induction t generalizing acc with
  | empty => rfl
  | node l x r hl hr => simp only [inorderInto, inorder, hl, hr, List.append_assoc, List.cons_append]

theorem externalLeaves_eq (t : Tree α) : externalLeaves t = size t + 1 := by
  induction t with
  | empty => rfl
  | node l x r hl hr => simp only [externalLeaves, size, hl, hr]; omega

end Tree
end JonnyLean.Trees
