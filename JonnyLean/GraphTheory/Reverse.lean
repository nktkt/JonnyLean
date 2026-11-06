import JonnyLean.GraphTheory.Morphism

namespace JonnyLean.GraphTheory

/-- Symmetry is separate data; directed graphs need not have it. -/
def Undirected (G : Graph V) : Prop := ∀ ⦃x y⦄, G.edge x y → G.edge y x

namespace Walk
variable {V : Type u} {G : Graph V} {x y z : V}

def reverse (sym : Undirected G) {x y : V} : Walk G x y → Walk G y x
  | .nil x => .nil x
  | .cons e p => (reverse sym p).append (.single (sym e))

@[simp] theorem reverse_nil (sym : Undirected G) (x : V) : reverse sym (.nil x) = .nil x := rfl
@[simp] theorem reverse_single (sym : Undirected G) (e : G.edge x y) :
    reverse sym (.single e) = .single (sym e) := rfl
@[simp] theorem length_reverse (sym : Undirected G) (p : Walk G x y) :
    (reverse sym p).length = p.length := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [reverse, length, ih]

theorem reverse_append (sym : Undirected G) (p : Walk G x y) (q : Walk G y z) :
    reverse sym (p.append q) = (reverse sym q).append (reverse sym p) := by
  induction p with
  | nil => simp [reverse]
  | cons e p ih => simp [append, reverse, ih, append_assoc]

@[simp] theorem reverse_reverse (sym : Undirected G) (p : Walk G x y) :
    reverse sym (reverse sym p) = p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [reverse, reverse_append, ih, single, append]

end Walk

theorem reachable_symm {G : Graph V} (sym : Undirected G) {x y : V}
    (h : Reachable G x y) : Reachable G y x := by
  obtain ⟨p⟩ := h
  exact ⟨p.reverse sym⟩

end JonnyLean.GraphTheory
