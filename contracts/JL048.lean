import JonnyLean.GraphTheory.Append

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.GraphTheory

theorem contract_JL048 {V : Type u} {G : Graph V} {x y z : V}
    (p : Walk G x y) (q : Walk G y z) :
    (p.append q).length = p.length + q.length := Walk.length_append p q

example {G : Graph V} {w x y z : V} (p : Walk G w x) (q : Walk G x y) (r : Walk G y z) :
    (p.append q).append r = p.append (q.append r) := Walk.append_assoc p q r
example {G : Graph V} {x y : V} (p : Walk G x y) : (Walk.nil x).append p = p := rfl
example {G : Graph V} {x y : V} (p : Walk G x y) : p.append (Walk.nil y) = p := Walk.append_nil p
example {G : Graph V} {w x y z : V} (e : G.edge w x) (p : Walk G x y) (q : Walk G y z) :
    (Walk.cons e p).append q = Walk.cons e (p.append q) := rfl

#print axioms JonnyLean.GraphTheory.Walk.length_append
#print axioms contract_JL048
