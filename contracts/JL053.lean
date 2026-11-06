import JonnyLean.GraphTheory.ClosedWalk

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.GraphTheory

theorem contract_JL053 {V : Type u} {G : Graph V} {x : V} (p : Walk G x x) (n : Nat) :
    (ClosedWalk.power p n).length = n * p.length := ClosedWalk.length_power p n

example {G : Graph V} {x : V} (p : Walk G x x) : ClosedWalk.power p 0 = Walk.nil x := rfl
example {G : Graph V} {x : V} (p : Walk G x x) (n : Nat) :
    ClosedWalk.power p (n + 1) = (ClosedWalk.power p n).append p := rfl
example {G : Graph V} {x : V} (p : Walk G x x) (m n : Nat) :
    ClosedWalk.power p (m + n) = (ClosedWalk.power p m).append (ClosedWalk.power p n) :=
  ClosedWalk.power_add p m n
example {G : Graph V} {x y : V} (p : Walk G x y) (q : Walk G y x) :
    (p.append q).length = (q.append p).length := ClosedWalk.rotation_length p q

#print axioms JonnyLean.GraphTheory.ClosedWalk.length_power
#print axioms contract_JL053
