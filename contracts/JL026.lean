import JonnyLean.Logic.Predicates

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-026. -/
theorem JL026 {α : Type u} (p q r : α → Prop) :
    ∀ x, (p x ∧ (q x ∨ r x)) ↔ ((p x ∧ q x) ∨ (p x ∧ r x)) :=
  JonnyLean.Predicate.meet_join_distrib p q r

example {α : Type u} (p q : α → Prop) :
    ∀ x, ¬ (p x ∨ q x) ↔ (¬ p x ∧ ¬ q x) :=
  JonnyLean.Predicate.complement_join p q
end JonnyLean.Contracts

#print axioms JonnyLean.Predicate.meet_join_distrib
#print axioms JonnyLean.Contracts.JL026
