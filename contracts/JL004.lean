import JonnyLean.FiniteSet.Basic

namespace JL004Contract
open JonnyLean

/-- The exact target expands cardinality and disjointness into list membership
and length, rather than trusting their local names. -/
theorem target {α : Type u} [DecidableEq α] :
    ∀ A B : FiniteSet α,
      (∀ x, x ∈ A.elems → x ∈ B.elems → False) →
      (FiniteSet.union A B).elems.length = A.elems.length + B.elems.length :=
  FiniteSet.card_union_of_disjoint

/-- The operation must be a true set union, including overlapping inputs. -/
theorem unionMembership {α : Type u} [DecidableEq α] :
    ∀ (A B : FiniteSet α) (x : α),
      x ∈ (FiniteSet.union A B).elems ↔ x ∈ A.elems ∨ x ∈ B.elems :=
  FiniteSet.mem_union

/-- No duplicated member may inflate the cardinality. -/
theorem unionNodup {α : Type u} [DecidableEq α] (A B : FiniteSet α) :
    (FiniteSet.union A B).elems.Nodup :=
  (FiniteSet.union A B).nodup

/-- Changing the enumeration order does not change cardinality. -/
theorem representationInvariant {α : Type u} :
    ∀ A B : FiniteSet α,
      (∀ x, x ∈ A.elems ↔ x ∈ B.elems) → A.elems.length = B.elems.length :=
  FiniteSet.card_eq_of_equivalent

def zero : FiniteSet Nat := FiniteSet.singleton 0
def one : FiniteSet Nat := FiniteSet.singleton 1

example : (FiniteSet.union (FiniteSet.empty : FiniteSet Nat) FiniteSet.empty).elems = [] := rfl
example : (FiniteSet.union FiniteSet.empty zero).elems = [0] := rfl
example : (FiniteSet.union zero FiniteSet.empty).elems = [0] := rfl
example : (FiniteSet.union zero one).elems = [0, 1] := rfl
example : (FiniteSet.union zero one).elems.length = 1 + 1 := by
  apply target
  intro x hx hy
  have hx0 : x = 0 := List.mem_singleton.mp hx
  have hx1 : x = 1 := List.mem_singleton.mp hy
  exact Nat.noConfusion (hx0.symm.trans hx1)

-- Overlap is a required boundary case: union must deduplicate.
example : (FiniteSet.union zero zero).elems = [0] := rfl
example : (FiniteSet.union zero zero).elems.length = 1 := rfl

end JL004Contract

#print axioms JonnyLean.FiniteSet.card_union_of_disjoint
#print axioms JL004Contract.target
#print axioms JL004Contract.unionMembership
#print axioms JL004Contract.unionNodup
#print axioms JL004Contract.representationInvariant
