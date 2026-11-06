import JonnyLean.GraphTheory.Basic

namespace JonnyLean.GraphTheory

/-- A finite directed walk. Vertices and edges may repeat; the empty walk is included. -/
inductive Walk (G : Graph V) : V → V → Type _ where
  | nil (x : V) : Walk G x x
  | cons {x y z : V} : G.edge x y → Walk G y z → Walk G x z

namespace Walk

variable {V : Type u} {G : Graph V} {w x y z : V}

def length {x y : V} : Walk G x y → Nat
  | .nil _ => 0
  | .cons _ p => p.length + 1

def single (e : G.edge x y) : Walk G x y := .cons e (.nil y)

def vertices {x y : V} : Walk G x y → List V
  | .nil x => [x]
  | @cons _ _ x _ _ _ p => x :: p.vertices

@[simp] theorem length_nil (G : Graph V) (x : V) : (nil (G := G) x).length = 0 := rfl
@[simp] theorem length_cons (e : G.edge x y) (p : Walk G y z) : (cons e p).length = p.length + 1 := rfl
@[simp] theorem length_single (e : G.edge x y) : (single e).length = 1 := rfl
@[simp] theorem vertices_length (p : Walk G x y) : p.vertices.length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [vertices, length, ih]

theorem endpoints_eq_of_length_zero (p : Walk G x y) (h : p.length = 0) : x = y := by
  cases p with
  | nil => rfl
  | cons e p => exact False.elim (Nat.noConfusion h)

theorem length_positive_of_ne (p : Walk G x y) (h : x ≠ y) : 0 < p.length := by
  cases p with
  | nil => exact False.elim (h rfl)
  | cons e p => exact Nat.zero_lt_succ _

end Walk
end JonnyLean.GraphTheory
