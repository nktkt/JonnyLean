import JonnyLean.Automata.Product

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Automata JonnyLean.Automata.Machine JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL153 (M : Machine α Q) (N : Machine α R) : (M.product N).language = inter M.language N.language := language_product M N

theorem contract_JL153_semantics (M : Machine α Q) (N : Machine α R) (q : Q) (r : R) (a : α) : (M.product N).step (q, r) a = (M.step q a, N.step r a) := rfl

theorem contract_JL153_boundary (M : Machine α Q) (N : Machine α R) : (M.product N).language [] ↔ M.language [] ∧ N.language [] := accepts_product M N []

#print axioms JonnyLean.Automata.Machine.language_product
#print axioms contract_JL153
#print axioms contract_JL153_semantics
#print axioms contract_JL153_boundary
