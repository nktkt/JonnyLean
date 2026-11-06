import JonnyLean.Automata.Restriction

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Automata JonnyLean.Automata.Machine JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL160 (M : Machine α Q) (P : Q → Prop) (hs : M.Stable P) (h0 : P M.start) : (M.restrict P hs h0).language = M.language := language_restrict M P hs h0

theorem contract_JL160_semantics (M : Machine α Q) (P : Q → Prop) (hs : M.Stable P) (h0 : P M.start) : (M.restrict P hs h0).start.val = M.start := rfl

theorem contract_JL160_boundary (M : Machine α Q) (states : List Q) (h0 : M.start ∈ states) : M.run M.start [] ∈ states := h0

#print axioms JonnyLean.Automata.Machine.language_restrict
#print axioms contract_JL160
#print axioms contract_JL160_semantics
#print axioms contract_JL160_boundary
