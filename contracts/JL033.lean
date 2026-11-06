import JonnyLean.Relations.Composition

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-033. -/
theorem JL033 {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}
    (r : α → β → Prop) (s : β → γ → Prop) (t : γ → δ → Prop) (a : α) (d : δ) :
    (∃ c, (∃ b, r a b ∧ s b c) ∧ t c d) ↔
    (∃ b, r a b ∧ (∃ c, s b c ∧ t c d)) :=
  JonnyLean.Relations.compose_assoc r s t a d

example {α : Type u} {β : Type v} (r : α → β → Prop) (a : α) (b : β) :
    (∃ x, a = x ∧ r x b) ↔ r a b :=
  JonnyLean.Relations.compose_equality_left r a b
end JonnyLean.Contracts

#print axioms JonnyLean.Relations.compose_assoc
#print axioms JonnyLean.Contracts.JL033
