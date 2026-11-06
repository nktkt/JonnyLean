import JonnyLean.GraphTheory.Walk

namespace JonnyLean.GraphTheory.Walk

variable {V : Type u} {G : Graph V} {w x y z : V}

def append {x y z : V} (p : Walk G x y) (q : Walk G y z) : Walk G x z :=
  match p with
  | .nil _ => q
  | .cons e p => .cons e (append p q)

@[simp] theorem nil_append (q : Walk G x y) : append (.nil x) q = q := rfl
@[simp] theorem cons_append (e : G.edge w x) (p : Walk G x y) (q : Walk G y z) :
    append (.cons e p) q = .cons e (append p q) := rfl
@[simp] theorem append_nil (p : Walk G x y) : append p (.nil y) = p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [append, ih]

theorem append_assoc (p : Walk G w x) (q : Walk G x y) (r : Walk G y z) :
    append (append p q) r = append p (append q r) := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [append, ih]

@[simp] theorem length_append (p : Walk G x y) (q : Walk G y z) :
    (append p q).length = p.length + q.length := by
  induction p with
  | nil => simp [append]
  | cons e p ih => simp [append, length, ih, Nat.add_assoc, Nat.add_comm]

theorem append_length_ge_left (p : Walk G x y) (q : Walk G y z) :
    p.length ≤ (append p q).length := by
  rw [length_append]
  exact Nat.le_add_right _ _

end JonnyLean.GraphTheory.Walk
