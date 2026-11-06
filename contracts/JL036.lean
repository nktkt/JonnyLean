import JonnyLean.Collections.Partition

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-036. -/
theorem JL036 {α : Type u} (p : α → Bool) (xs : List α) :
    ((JonnyLean.Collections.partition p xs).1 ++
      (JonnyLean.Collections.partition p xs).2).Perm xs :=
  JonnyLean.Collections.partition_perm p xs

example : JonnyLean.Collections.partition (fun n : Nat => n % 2 == 0) [3, 2, 1, 4] =
    ([2, 4], [3, 1]) := by decide

example {α : Type u} (p : α → Bool) :
    JonnyLean.Collections.partition p ([] : List α) = ([], []) := rfl
end JonnyLean.Contracts

#print axioms JonnyLean.Collections.partition_perm
#print axioms JonnyLean.Contracts.JL036
