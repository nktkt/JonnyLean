import JonnyLean.Automata.Equivalence

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Automata JonnyLean.Automata.Machine JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL159 (M : Machine α Q) {q r : Q} (h : ∀ w, M.accept (M.run q w) = M.accept (M.run r w)) (u : List α) : M.Equivalent (M.run q u) (M.run r u) := equivalent_run M h u

theorem contract_JL159_semantics (M : Machine α Q) (q r : Q) : M.Equivalent q r ↔ ∀ w, M.accept (M.run q w) = M.accept (M.run r w) := Iff.rfl

theorem contract_JL159_boundary (M : Machine α Q) (q : Q) : M.Equivalent q q := equivalent_refl M q

#print axioms JonnyLean.Automata.Machine.equivalent_run
#print axioms contract_JL159
#print axioms contract_JL159_semantics
#print axioms contract_JL159_boundary
