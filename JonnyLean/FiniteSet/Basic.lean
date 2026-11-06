import Init.Data.List.Pairwise
import Init.Data.List.Perm

namespace JonnyLean

/-- A finite set represented by a list with a proof that no element is repeated.
The order is representation data; `FiniteSet.Equivalent` expresses set equality. -/
structure FiniteSet (α : Type u) where
  elems : List α
  nodup : elems.Nodup

namespace FiniteSet

instance : Membership α (FiniteSet α) := ⟨fun A x => x ∈ A.elems⟩

/-- The number of distinct members. -/
def card (A : FiniteSet α) : Nat := A.elems.length

/-- Extensional equality ignores the enumeration order. -/
def Equivalent (A B : FiniteSet α) : Prop := ∀ x, x ∈ A ↔ x ∈ B

/-- Inclusion concerns membership, not enumeration order. -/
def Subset (A B : FiniteSet α) : Prop := ∀ x, x ∈ A → x ∈ B

/-- Two sets are disjoint when they have no common member. -/
def Disjoint (A B : FiniteSet α) : Prop := ∀ x, x ∈ A → x ∈ B → False

def empty : FiniteSet α := ⟨[], List.nodup_nil⟩

def singleton (x : α) : FiniteSet α :=
  ⟨[x], List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩

/-- Filter the right enumeration before appending, so union works even for
sets that are not disjoint. -/
def union [DecidableEq α] (A B : FiniteSet α) : FiniteSet α where
  elems := A.elems ++ B.elems.filter (fun x => decide (x ∉ A.elems))
  nodup := by
    apply List.nodup_append.mpr
    refine ⟨A.nodup, List.Pairwise.filter _ B.nodup, ?_⟩
    intro a ha b hb hab
    have hnot : b ∉ A.elems := (of_decide_eq_true (List.mem_filter.mp hb).2)
    exact hnot (hab ▸ ha)

/-- Union has precisely the usual membership semantics. -/
theorem mem_union [DecidableEq α] (A B : FiniteSet α) (x : α) :
    x ∈ union A B ↔ x ∈ A ∨ x ∈ B := by
  change x ∈ A.elems ++ B.elems.filter _ ↔ x ∈ A.elems ∨ x ∈ B.elems
  simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h
    cases h with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr h.1
  · intro h
    cases h with
    | inl h => exact Or.inl h
    | inr h =>
      by_cases ha : x ∈ A.elems
      · exact Or.inl ha
      · exact Or.inr ⟨h, ha⟩

/-- Cardinalities add when the two finite sets have no common member. -/
theorem card_union_of_disjoint [DecidableEq α] (A B : FiniteSet α)
    (h : Disjoint A B) : card (union A B) = card A + card B := by
  have hf : B.elems.filter (fun x => decide (x ∉ A.elems)) = B.elems := by
    apply List.filter_eq_self.mpr
    intro x hx
    exact decide_eq_true (fun ha => h x ha hx)
  change (A.elems ++ B.elems.filter _).length = A.elems.length + B.elems.length
  rw [hf, List.length_append]

/-- Duplicate-free enumerations with the same members are permutations.
The proof uses the membership witness directly, without classical choice. -/
theorem perm_of_members (xs ys : List α) (hx : xs.Nodup) (hy : ys.Nodup)
    (h : ∀ x, x ∈ xs ↔ x ∈ ys) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    have he : ys = [] := List.eq_nil_of_subset_nil (fun {x} hx => (h x).mpr hx)
    cases he
    exact List.Perm.nil
  | cons a xs ih =>
    obtain ⟨left, right, rfl⟩ := List.append_of_mem ((h a).mp List.mem_cons_self)
    have hp : (left ++ a :: right).Perm (a :: (left ++ right)) := List.perm_middle
    have hyn := hp.nodup hy
    have hxt := (List.nodup_cons.mp hx).2
    have hyt := (List.nodup_cons.mp hyn).2
    have he : ∀ x, x ∈ xs ↔ x ∈ left ++ right := by
      intro x
      constructor
      · intro hm
        have hc := hp.mem_iff.mp ((h x).mp (List.mem_cons_of_mem a hm))
        cases List.mem_cons.mp hc with
        | inl ha => exact False.elim ((List.nodup_cons.mp hx).1 (ha ▸ hm))
        | inr ht => exact ht
      · intro hm
        have hc := (h x).mpr (hp.mem_iff.mpr (List.mem_cons_of_mem a hm))
        cases List.mem_cons.mp hc with
        | inl ha => exact False.elim ((List.nodup_cons.mp hyn).1 (ha ▸ hm))
        | inr ht => exact ht
    exact ((ih (left ++ right) hxt hyt he).cons a).trans hp.symm

/-- Cardinality does not depend on the chosen duplicate-free enumeration. -/
theorem card_eq_of_equivalent (A B : FiniteSet α)
    (h : Equivalent A B) : card A = card B :=
  (perm_of_members A.elems B.elems A.nodup B.nodup h).length_eq

end FiniteSet
end JonnyLean
