import JonnyLean

namespace JL005Contract
open JonnyLean

/-- The target counts the actual duplicate-free powerset enumeration. -/
theorem target {α : Type u} :
    ∀ A : FiniteSet α,
      (FiniteSet.powerset A).elems.length = 2 ^ A.elems.length :=
  FiniteSet.card_powerset

/-- The enumeration consists exactly of source-order subsequences. -/
theorem canonicalMembership {α : Type u} :
    ∀ A B : FiniteSet α,
      B ∈ (FiniteSet.powerset A).elems ↔ B.elems.Sublist A.elems :=
  FiniteSet.mem_powerset

/-- Every counted object is a subset in the ordinary membership sense. -/
theorem soundness {α : Type u} :
    ∀ A B : FiniteSet α,
      B ∈ (FiniteSet.powerset A).elems →
      ∀ x, x ∈ B.elems → x ∈ A.elems :=
  FiniteSet.powerset_sound

/-- All finite subsets occur, even when their own enumeration has another order. -/
theorem completeness {α : Type u} [DecidableEq α] :
    ∀ A B : FiniteSet α,
      (∀ x, x ∈ B.elems → x ∈ A.elems) →
      ∃ C : FiniteSet α, C ∈ (FiniteSet.powerset A).elems ∧
        (∀ x, x ∈ B.elems ↔ x ∈ C.elems) :=
  FiniteSet.powerset_complete

/-- Two representations of the same mathematical subset cannot both be counted. -/
theorem uniqueRepresentation {α : Type u} :
    ∀ A B C : FiniteSet α,
      B ∈ (FiniteSet.powerset A).elems →
      C ∈ (FiniteSet.powerset A).elems →
      (∀ x, x ∈ B.elems ↔ x ∈ C.elems) → B = C :=
  FiniteSet.powerset_unique

theorem enumerationNodup {α : Type u} (A : FiniteSet α) :
    (FiniteSet.powerset A).elems.Nodup :=
  (FiniteSet.powerset A).nodup

def pair : FiniteSet Nat := ⟨[0, 1], by decide⟩
def reversedPair : FiniteSet Nat := ⟨[1, 0], by decide⟩

example : (FiniteSet.powerset (FiniteSet.empty : FiniteSet Nat)).elems.length = 1 := rfl
example : FiniteSet.empty ∈ (FiniteSet.powerset (FiniteSet.empty : FiniteSet Nat)).elems :=
  List.mem_cons_self
example : (FiniteSet.powerset (FiniteSet.singleton 0)).elems.length = 2 := rfl
example : (FiniteSet.powerset pair).elems.length = 4 := rfl
example : (FiniteSet.powerset pair).elems.map FiniteSet.elems = [[], [1], [0], [0, 1]] := rfl

-- A differently ordered representation still has a representative in the powerset.
example : ∃ C : FiniteSet Nat, C ∈ (FiniteSet.powerset pair).elems ∧
    (∀ x, x ∈ reversedPair.elems ↔ x ∈ C.elems) := by
  apply completeness
  intro x hx
  simp only [reversedPair, pair, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  exact hx.elim Or.inr Or.inl

end JL005Contract

#print axioms JonnyLean.FiniteSet.card_powerset
#print axioms JL005Contract.target
#print axioms JL005Contract.canonicalMembership
#print axioms JL005Contract.soundness
#print axioms JL005Contract.completeness
#print axioms JL005Contract.uniqueRepresentation
#print axioms JL005Contract.enumerationNodup
