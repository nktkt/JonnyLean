import JonnyLean.GraphTheory.Walk

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.GraphTheory

theorem contract_JL047 {V : Type u} {G : Graph V} {x y : V} (p : Walk G x y) :
    p.vertices.length = p.length + 1 := Walk.vertices_length p

example (G : Graph V) (x : V) : (Walk.nil (G := G) x).vertices = [x] := rfl
example (G : Graph V) (x : V) : (Walk.nil (G := G) x).length = 0 := rfl
example {G : Graph V} {x y z : V} (e : G.edge x y) (p : Walk G y z) :
    (Walk.cons e p).vertices = x :: p.vertices := rfl
example {G : Graph V} {x y z : V} (e : G.edge x y) (p : Walk G y z) :
    (Walk.cons e p).length = p.length + 1 := rfl
example {G : Graph V} {x y : V} (p : Walk G x y) : p.length = 0 → x = y :=
  Walk.endpoints_eq_of_length_zero p

#print axioms JonnyLean.GraphTheory.Walk.vertices_length
#print axioms contract_JL047
