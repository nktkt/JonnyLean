import JonnyLean.GraphTheory.Subgraph

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.GraphTheory

theorem contract_JL054 {V : Type u} (x y : V) :
    Nonempty (Walk (Graph.mk (fun _ _ : V => False)) x y) ↔ x = y := reachable_empty_iff x y

example {G H : Graph V} (h : ∀ ⦃x y⦄, G.edge x y → H.edge x y) {x y : V} :
    Nonempty (Walk G x y) → Nonempty (Walk H x y) := reachable_mono h
example {G H : Graph V} (h : Graph.Subgraph G H) (x : V) : (inclusion h).vertex x = x := rfl
example : ¬ Reachable (Graph.empty : Graph Bool) false true := by
  intro h
  have := (reachable_empty_iff false true).mp h
  cases this
example : Reachable (Graph.empty : Graph Bool) false false := reachable_refl _ _
example : Reachable (Graph.complete : Graph Bool) false true := reachable_complete _ _

#print axioms JonnyLean.GraphTheory.reachable_empty_iff
#print axioms contract_JL054
