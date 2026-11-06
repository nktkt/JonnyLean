import Std
import JonnyLean.FiniteSet.Basic

namespace JonnyLean.FiniteSet

def intersection [DecidableEq α] (A B : FiniteSet α) : FiniteSet α where
  elems := A.elems.filter (fun x => decide (x ∈ B.elems))
  nodup := A.nodup.filter _

theorem mem_intersection [DecidableEq α] (A B : FiniteSet α) (x : α) :
    x ∈ intersection A B ↔ x ∈ A ∧ x ∈ B := by
  change x ∈ A.elems.filter _ ↔ x ∈ A.elems ∧ x ∈ B.elems
  simp

theorem intersection_greatest [DecidableEq α] (A B C : FiniteSet α) :
    Subset C (intersection A B) ↔ Subset C A ∧ Subset C B := by
  constructor
  · intro h
    exact ⟨fun x hx => ((mem_intersection A B x).mp (h x hx)).1,
      fun x hx => ((mem_intersection A B x).mp (h x hx)).2⟩
  · intro h x hx; exact (mem_intersection A B x).mpr ⟨h.1 x hx, h.2 x hx⟩

theorem intersection_comm [DecidableEq α] (A B : FiniteSet α) :
    Equivalent (intersection A B) (intersection B A) := by
  intro x; simp only [mem_intersection, and_comm]

theorem intersection_union_distrib [DecidableEq α] (A B C : FiniteSet α) :
    Equivalent (intersection A (union B C)) (union (intersection A B) (intersection A C)) := by
  intro x; simp only [mem_intersection, mem_union, and_or_left]

theorem intersection_mono [DecidableEq α] {A B C D : FiniteSet α}
    (hab : Subset A B) (hcd : Subset C D) : Subset (intersection A C) (intersection B D) := by
  intro x hx
  have h := (mem_intersection A C x).mp hx
  exact (mem_intersection B D x).mpr ⟨hab x h.1, hcd x h.2⟩

end JonnyLean.FiniteSet
