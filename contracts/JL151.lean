import JonnyLean.Automata.Run

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Automata JonnyLean.Automata.Machine JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL151 (M : Machine α Q) (q : Q) (u v : List α) : M.run q (u ++ v) = M.run (M.run q u) v := run_append M q u v

theorem contract_JL151_semantics (M : Machine α Q) (q : Q) (a : α) (w : List α) : M.run q (a :: w) = M.run (M.step q a) w := rfl

theorem contract_JL151_boundary (M : Machine α Q) (q : Q) : M.run q [] = q := rfl

#print axioms JonnyLean.Automata.Machine.run_append
#print axioms contract_JL151
#print axioms contract_JL151_semantics
#print axioms contract_JL151_boundary
