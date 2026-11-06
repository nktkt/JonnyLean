import JonnyLean.Automata.InputMap

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Automata JonnyLean.Automata.Machine JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL156 (M : Machine β Q) (f : α → β) (q : Q) (w : List α) : (M.comap f).run q w = M.run q (w.map f) := run_comap M f q w

theorem contract_JL156_semantics (M : Machine β Q) (f : α → β) (q : Q) (a : α) : (M.comap f).step q a = M.step q (f a) := rfl

theorem contract_JL156_boundary (M : Machine α Q) : M.comap id = M := comap_id M

#print axioms JonnyLean.Automata.Machine.run_comap
#print axioms contract_JL156
#print axioms contract_JL156_semantics
#print axioms contract_JL156_boundary
