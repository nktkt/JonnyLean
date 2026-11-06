import JonnyLean.GraphTheory.Reachability

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.GraphTheory

theorem contract_JL049 {V : Type u} {G : Graph V} {x y : V}
    (R : V → V → Prop) (hr : ∀ x, R x x)
    (ht : ∀ x y z, R x y → R y z → R x z)
    (he : ∀ x y, G.edge x y → R x y) : Nonempty (Walk G x y) → R x y :=
  reachable_minimal R hr ht he

example (G : Graph V) (x y : V) : Reachable G x y ↔ Nonempty (Walk G x y) := Iff.rfl
example (G : Graph V) (x : V) : Nonempty (Walk G x x) := reachable_refl G x
example {G : Graph V} {x y z : V} :
    Nonempty (Walk G x y) → Nonempty (Walk G y z) → Nonempty (Walk G x z) := reachable_trans
example (G : Graph V) (x z : V) : Nonempty (Walk G x z) ↔
    x = z ∨ ∃ y, G.edge x y ∧ Nonempty (Walk G y z) := reachable_iff G x z

#print axioms JonnyLean.GraphTheory.reachable_minimal
#print axioms contract_JL049
