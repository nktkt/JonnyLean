import JonnyLean.GraphTheory.Reverse

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.GraphTheory

theorem contract_JL051 {V : Type u} {G : Graph V}
    (sym : ∀ ⦃x y⦄, G.edge x y → G.edge y x) {x y : V} (p : Walk G x y) :
    (p.reverse sym).reverse sym = p := Walk.reverse_reverse sym p

example (G : Graph V) : Undirected G ↔ ∀ ⦃x y⦄, G.edge x y → G.edge y x := Iff.rfl
example {G : Graph V} (sym : Undirected G) (x : V) : (Walk.nil x).reverse sym = Walk.nil x := rfl
example {G : Graph V} (sym : Undirected G) {x y z : V} (p : Walk G x y) (q : Walk G y z) :
    (p.append q).reverse sym = (q.reverse sym).append (p.reverse sym) := Walk.reverse_append sym p q
example {G : Graph V} (sym : Undirected G) {x y : V} (p : Walk G x y) :
    (p.reverse sym).length = p.length := Walk.length_reverse sym p

#print axioms JonnyLean.GraphTheory.Walk.reverse_reverse
#print axioms contract_JL051
