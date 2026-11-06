import JonnyLean.GraphTheory.ClosedWalk

namespace JonnyLean.GraphTheory

variable {V : Type u} {G H : Graph V} {x y : V}

/-- Inclusion of edges induces an identity-on-vertices graph homomorphism. -/
def inclusion (h : Graph.Subgraph G H) : Hom G H := ⟨fun x => x, fun e => h e⟩

theorem reachable_mono (h : Graph.Subgraph G H) (r : Reachable G x y) : Reachable H x y :=
  (inclusion h).preserves_reachable r

theorem component_mono (h : Graph.Subgraph G H) (r : SameComponent G x y) : SameComponent H x y :=
  (inclusion h).preserves_component r

theorem reachable_union_left (H : Graph V) (r : Reachable G x y) : Reachable (G.union H) x y :=
  reachable_mono (fun _ _ e => Or.inl e) r

theorem reachable_union_right (G : Graph V) (r : Reachable H x y) : Reachable (G.union H) x y :=
  reachable_mono (fun _ _ e => Or.inr e) r

theorem empty_walk_endpoints (p : Walk (Graph.empty : Graph V) x y) : x = y := by
  cases p with
  | nil => rfl
  | cons e p => exact False.elim e

theorem reachable_empty_iff (x y : V) : Reachable Graph.empty x y ↔ x = y := by
  constructor
  · rintro ⟨p⟩
    exact empty_walk_endpoints p
  · intro h
    cases h
    exact reachable_refl _ _

theorem component_empty_iff (x y : V) : SameComponent Graph.empty x y ↔ x = y := by
  constructor
  · intro h
    exact (reachable_empty_iff x y).mp h.1
  · intro h
    cases h
    exact component_refl _ _

theorem reachable_complete (x y : V) : Reachable Graph.complete x y := reachable_of_edge True.intro

end JonnyLean.GraphTheory
