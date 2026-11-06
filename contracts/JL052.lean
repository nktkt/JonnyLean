import JonnyLean.GraphTheory.Components

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.GraphTheory

theorem contract_JL052 {V : Type u} (G : Graph V) :
    Equivalence (fun x y => Nonempty (Walk G x y) ∧ Nonempty (Walk G y x)) :=
  component_equivalence G

example (G : Graph V) (x y : V) : SameComponent G x y ↔
    Nonempty (Walk G x y) ∧ Nonempty (Walk G y x) := Iff.rfl
example {G : Graph V} {x y z : V} (h : SameComponent G x y) :
    Reachable G x z ↔ Reachable G y z := reachable_iff_of_component h
example {G : Graph V} (sym : Undirected G) {x y : V} :
    SameComponent G x y ↔ Reachable G x y := component_iff_reachable sym
example (G : Graph V) (x : V) : SameComponent G x x := component_refl G x

#print axioms JonnyLean.GraphTheory.component_equivalence
#print axioms contract_JL052
