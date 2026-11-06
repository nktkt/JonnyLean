import JonnyLean.Collections.Intersection

namespace JonnyLean.FiniteSet

def difference [DecidableEq α] (A B : FiniteSet α) : FiniteSet α where
  elems := A.elems.filter (fun x => decide (x ∉ B.elems))
  nodup := A.nodup.filter _

theorem mem_difference [DecidableEq α] (A B : FiniteSet α) (x : α) :
    x ∈ difference A B ↔ x ∈ A ∧ x ∉ B := by
  change x ∈ A.elems.filter _ ↔ x ∈ A.elems ∧ x ∉ B.elems
  simp

theorem intersection_difference_disjoint [DecidableEq α] (A B : FiniteSet α) :
    Disjoint (intersection A B) (difference A B) := by
  intro x hi hd
  exact ((mem_difference A B x).mp hd).2 ((mem_intersection A B x).mp hi).2

theorem intersection_difference_cover [DecidableEq α] (A B : FiniteSet α) :
    Equivalent (union (intersection A B) (difference A B)) A := by
  intro x
  rw [mem_union, mem_intersection, mem_difference]
  constructor
  · intro h; exact h.elim And.left And.left
  · intro hx
    by_cases hb : x ∈ B.elems
    · exact Or.inl ⟨hx, hb⟩
    · exact Or.inr ⟨hx, hb⟩

theorem card_intersection_add_difference [DecidableEq α] (A B : FiniteSet α) :
    card (intersection A B) + card (difference A B) = card A := by
  calc _ = card (union (intersection A B) (difference A B)) :=
         (card_union_of_disjoint _ _ (intersection_difference_disjoint A B)).symm
       _ = card A := card_eq_of_equivalent _ _ (intersection_difference_cover A B)

theorem difference_union [DecidableEq α] (A B C : FiniteSet α) :
    Equivalent (difference A (union B C)) (intersection (difference A B) (difference A C)) := by
  intro x
  simp only [mem_difference, mem_union, mem_intersection]
  constructor
  · intro ⟨ha, hn⟩; exact ⟨⟨ha, fun hb => hn (Or.inl hb)⟩, ⟨ha, fun hc => hn (Or.inr hc)⟩⟩
  · intro ⟨⟨ha, hb⟩, ⟨_, hc⟩⟩; exact ⟨ha, fun h => h.elim hb hc⟩

end JonnyLean.FiniteSet
