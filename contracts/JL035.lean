import JonnyLean.Relations.Invariants

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-035. -/
theorem JL035 {α : Type u} (r : α → α → Prop) (p : α → Prop)
    (step : ∀ a b, p a → r a b → p b) (a b : α)
    (path : JonnyLean.Relations.Reach r a b) (ha : p a) : p b :=
  JonnyLean.Relations.reach_preserves step path ha

example {α : Type u} (r : α → α → Prop) (p : α → Prop)
    (step : ∀ a b, p a → r a b → p b) (a b : α) (ha : p a) (hb : ¬ p b) :
    ¬ JonnyLean.Relations.Reach r a b :=
  JonnyLean.Relations.unreachable_of_invariant step ha hb
end JonnyLean.Contracts

#print axioms JonnyLean.Relations.reach_preserves
#print axioms JonnyLean.Contracts.JL035
