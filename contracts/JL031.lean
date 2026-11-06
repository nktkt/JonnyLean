import JonnyLean.Functions.Retractions

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-031. -/
theorem JL031 {α : Type u} (p q : α → α)
    (hp : ∀ x, p (p x) = p x) (hq : ∀ x, q (q x) = q x)
    (hc : ∀ x, p (q x) = q (p x)) :
    ∀ x, p (q (p (q x))) = p (q x) :=
  JonnyLean.Functions.commuting_idempotents hp hq hc

example {α : Type u} {β : Type v} (s : β → α) (r : α → β)
    (h : ∀ b, r (s b) = b) : ∀ a, s (r (s (r a))) = s (r a) :=
  JonnyLean.Functions.retraction_idempotent h
end JonnyLean.Contracts

#print axioms JonnyLean.Functions.commuting_idempotents
#print axioms JonnyLean.Contracts.JL031
