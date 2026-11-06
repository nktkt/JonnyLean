import JonnyLean.Automata.Complement

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Automata JonnyLean.Automata.Machine JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL154 (M : Machine α Q) (w : List α) : M.complement.language w ↔ ¬M.language w := language_complement M w

theorem contract_JL154_semantics (M : Machine α Q) (q : Q) : M.complement.accept q = Bool.not (M.accept q) := rfl

theorem contract_JL154_boundary (M : Machine α Q) : M.complement.complement = M := complement_complement M

#print axioms JonnyLean.Automata.Machine.language_complement
#print axioms contract_JL154
#print axioms contract_JL154_semantics
#print axioms contract_JL154_boundary
