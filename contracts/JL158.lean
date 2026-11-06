import JonnyLean.Automata.Reachability

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Automata JonnyLean.Automata.Machine JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL158 (M : Machine α Q) (P : Q → Prop) (hs : M.Stable P) (h0 : P M.start) : ∀ q, M.Reachable q → P q := reachable_minimal M P hs h0

theorem contract_JL158_semantics (M : Machine α Q) (q : Q) : M.Reachable q ↔ ∃ w, M.run M.start w = q := Iff.rfl

theorem contract_JL158_boundary (M : Machine α Q) : M.Reachable M.start := reachable_start M

#print axioms JonnyLean.Automata.Machine.reachable_minimal
#print axioms contract_JL158
#print axioms contract_JL158_semantics
#print axioms contract_JL158_boundary
