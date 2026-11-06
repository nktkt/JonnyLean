import JonnyLean.Automata.Homomorphism

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Automata JonnyLean.Automata.Machine JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL155 {M : Machine α Q} {N : Machine α R} (f : Hom M N) : M.language = N.language := Hom.language_eq f

theorem contract_JL155_semantics {M : Machine α Q} {N : Machine α R} (f : Hom M N) (q : Q) (a : α) : f.state (M.step q a) = N.step (f.state q) a := f.step q a

theorem contract_JL155_boundary (M : Machine α Q) (q : Q) : (Hom.id M).state q = q := rfl

#print axioms JonnyLean.Automata.Hom.language_eq
#print axioms contract_JL155
#print axioms contract_JL155_semantics
#print axioms contract_JL155_boundary
