import JonnyLean.Automata.Language

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Automata JonnyLean.Automata.Machine JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL152 (M : Machine α Q) (u : List α) : leftQuotient u M.language = (M.restart (M.run M.start u)).language := language_residual M u

theorem contract_JL152_semantics (M : Machine α Q) (w : List α) : M.language w ↔ M.accept (M.run M.start w) = true := Iff.rfl

theorem contract_JL152_boundary (M : Machine α Q) : M.language [] ↔ M.accept M.start = true := Iff.rfl

#print axioms JonnyLean.Automata.Machine.language_residual
#print axioms contract_JL152
#print axioms contract_JL152_semantics
#print axioms contract_JL152_boundary
