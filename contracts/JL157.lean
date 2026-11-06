import JonnyLean.Automata.Invariants

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Automata JonnyLean.Automata.Machine JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL157 (M : Machine α Q) (P : Q → Prop) (hs : ∀ q a, P q → P (M.step q a)) (q : Q) (hq : P q) (w : List α) : P (M.run q w) := run_invariant M P hs q hq w

theorem contract_JL157_semantics (M : Machine α Q) (P : Q → Prop) : M.Stable P ↔ ∀ q a, P q → P (M.step q a) := Iff.rfl

theorem contract_JL157_boundary (M : Machine α Q) (P : Q → Prop) (q : Q) (hq : P q) : P (M.run q []) := hq

#print axioms JonnyLean.Automata.Machine.run_invariant
#print axioms contract_JL157
#print axioms contract_JL157_semantics
#print axioms contract_JL157_boundary
