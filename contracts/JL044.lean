import JonnyLean.Algorithms.Deduplicate

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-044. -/
theorem JL044 {α : Type u} [DecidableEq α] (xs : List α) :
    (JonnyLean.Algorithms.deduplicate xs).Nodup :=
  JonnyLean.Algorithms.deduplicate_nodup xs

theorem JL044_members {α : Type u} [DecidableEq α] (x : α) (xs : List α) :
    x ∈ JonnyLean.Algorithms.deduplicate xs ↔ x ∈ xs :=
  JonnyLean.Algorithms.mem_deduplicate x xs

example : JonnyLean.Algorithms.deduplicate [1, 2, 1, 3, 2] = [1, 3, 2] := by decide

example {α : Type u} [DecidableEq α] :
    JonnyLean.Algorithms.deduplicate ([] : List α) = [] := rfl
end JonnyLean.Contracts

#print axioms JonnyLean.Algorithms.deduplicate_nodup
#print axioms JonnyLean.Contracts.JL044
