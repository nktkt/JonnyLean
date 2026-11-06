import JonnyLean.GraphTheory.Basic

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.GraphTheory

theorem contract_JL046 {V : Type u} {G H : Graph V} :
    (∀ x y, G.edge x y → H.edge x y) →
    (∀ x y, H.edge x y → G.edge x y) → G = H := by
  intro h k
  exact Graph.subgraph_antisymm (fun x y => h x y) (fun x y => k x y)

example (G H : Graph V) (x y : V) : (G.union H).edge x y ↔ G.edge x y ∨ H.edge x y := Iff.rfl
example (G H : Graph V) (x y : V) : (G.inter H).edge x y ↔ G.edge x y ∧ H.edge x y := Iff.rfl
example (G : Graph V) (x y : V) : G.transpose.edge x y ↔ G.edge y x := Iff.rfl
example (x : V) : ¬ (Graph.empty : Graph V).edge x x := fun h => h
example (x : V) : (Graph.complete : Graph V).edge x x := True.intro

#print axioms JonnyLean.GraphTheory.Graph.subgraph_antisymm
#print axioms contract_JL046
