import JonnyLean.GraphTheory.Reachability

namespace JonnyLean.GraphTheory

/-- An edge-preserving vertex map; neither injectivity nor surjectivity is required. -/
structure Hom (G : Graph V) (H : Graph W) where
  vertex : V → W
  edge : ∀ {x y}, G.edge x y → H.edge (vertex x) (vertex y)

namespace Hom
variable {V : Type u} {W : Type v} {U : Type w}
variable {G : Graph V} {H : Graph W} {K : Graph U} {x y z : V}

def id (G : Graph V) : Hom G G := ⟨fun x => x, fun e => e⟩
def comp (g : Hom H K) (f : Hom G H) : Hom G K :=
  ⟨fun x => g.vertex (f.vertex x), fun e => g.edge (f.edge e)⟩

def mapWalk (f : Hom G H) {x y : V} : Walk G x y → Walk H (f.vertex x) (f.vertex y)
  | .nil x => .nil (f.vertex x)
  | .cons e p => .cons (f.edge e) (f.mapWalk p)

@[simp] theorem mapWalk_nil (f : Hom G H) (x : V) : f.mapWalk (.nil x) = .nil (f.vertex x) := rfl
@[simp] theorem length_mapWalk (f : Hom G H) (p : Walk G x y) : (f.mapWalk p).length = p.length := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [mapWalk, Walk.length, ih]

theorem mapWalk_append (f : Hom G H) (p : Walk G x y) (q : Walk G y z) :
    f.mapWalk (p.append q) = (f.mapWalk p).append (f.mapWalk q) := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [mapWalk, Walk.append, ih]

@[simp] theorem mapWalk_id (p : Walk G x y) : (id G).mapWalk p = p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [mapWalk]
    rw [ih]
    rfl

theorem mapWalk_comp (g : Hom H K) (f : Hom G H) (p : Walk G x y) :
    (comp g f).mapWalk p = g.mapWalk (f.mapWalk p) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [mapWalk]
    rw [ih]
    rfl

theorem preserves_reachable (f : Hom G H) (h : Reachable G x y) :
    Reachable H (f.vertex x) (f.vertex y) := by
  obtain ⟨p⟩ := h
  exact ⟨f.mapWalk p⟩

end Hom
end JonnyLean.GraphTheory
