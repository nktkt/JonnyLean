import JonnyLean.GraphTheory.Morphism

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.GraphTheory

theorem contract_JL050 {V : Type u} {W : Type v} {G : Graph V} {H : Graph W}
    (f : Hom G H) {x y : V} (p : Walk G x y) :
    (f.mapWalk p).length = p.length := Hom.length_mapWalk f p

example {G : Graph V} {H : Graph W} (f : Hom G H) (x : V) :
    f.mapWalk (Walk.nil x) = Walk.nil (f.vertex x) := rfl
example {G : Graph V} {H : Graph W} (f : Hom G H) {x y z : V}
    (e : G.edge x y) (p : Walk G y z) :
    f.mapWalk (Walk.cons e p) = Walk.cons (f.edge e) (f.mapWalk p) := rfl
example {G : Graph V} {H : Graph W} (f : Hom G H) {x y : V} :
    Nonempty (Walk G x y) → Nonempty (Walk H (f.vertex x) (f.vertex y)) := f.preserves_reachable
example {G : Graph V} {x y : V} (p : Walk G x y) : (Hom.id G).mapWalk p = p := Hom.mapWalk_id p

#print axioms JonnyLean.GraphTheory.Hom.length_mapWalk
#print axioms contract_JL050
