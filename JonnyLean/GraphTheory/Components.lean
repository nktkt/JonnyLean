import JonnyLean.GraphTheory.Reverse

namespace JonnyLean.GraphTheory

variable {V : Type u} {W : Type v} {G : Graph V} {H : Graph W} {x y z : V}

/-- Belonging to the same strongly connected component; no quotient or choices are used. -/
def SameComponent (G : Graph V) (x y : V) : Prop := Reachable G x y ∧ Reachable G y x

theorem component_refl (G : Graph V) (x : V) : SameComponent G x x :=
  ⟨reachable_refl G x, reachable_refl G x⟩
theorem component_symm (h : SameComponent G x y) : SameComponent G y x := ⟨h.2, h.1⟩
theorem component_trans (h : SameComponent G x y) (k : SameComponent G y z) : SameComponent G x z :=
  ⟨reachable_trans h.1 k.1, reachable_trans k.2 h.2⟩
theorem component_equivalence (G : Graph V) : Equivalence (SameComponent G) :=
  ⟨component_refl G, component_symm, component_trans⟩

theorem component_iff_reachable (sym : Undirected G) : SameComponent G x y ↔ Reachable G x y :=
  ⟨And.left, fun h => ⟨h, reachable_symm sym h⟩⟩

theorem Hom.preserves_component (f : Hom G H) (h : SameComponent G x y) :
    SameComponent H (f.vertex x) (f.vertex y) :=
  ⟨f.preserves_reachable h.1, f.preserves_reachable h.2⟩

/-- A component has the same outgoing reachability set from every one of its vertices. -/
theorem reachable_iff_of_component (h : SameComponent G x y) :
    Reachable G x z ↔ Reachable G y z :=
  ⟨fun k => reachable_trans h.2 k, fun k => reachable_trans h.1 k⟩

theorem component_members_iff (h : SameComponent G x y) :
    SameComponent G x z ↔ SameComponent G y z :=
  ⟨fun k => component_trans (component_symm h) k, fun k => component_trans h k⟩

end JonnyLean.GraphTheory
