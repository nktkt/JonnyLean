namespace JonnyLean.GraphTheory

/-- A directed graph, permitting loops and arbitrary vertex types. -/
structure Graph (V : Type u) where
  edge : V → V → Prop

namespace Graph

def empty : Graph V := ⟨fun _ _ => False⟩
def complete : Graph V := ⟨fun _ _ => True⟩
def union (G H : Graph V) : Graph V := ⟨fun x y => G.edge x y ∨ H.edge x y⟩
def inter (G H : Graph V) : Graph V := ⟨fun x y => G.edge x y ∧ H.edge x y⟩
def transpose (G : Graph V) : Graph V := ⟨fun x y => G.edge y x⟩
def Subgraph (G H : Graph V) : Prop := ∀ ⦃x y⦄, G.edge x y → H.edge x y

theorem ext {G H : Graph V} (h : ∀ x y, G.edge x y ↔ H.edge x y) : G = H := by
  cases G with
  | mk g =>
    cases H with
    | mk h' =>
      have hEdge : g = h' :=
        funext (fun x => funext (fun y => propext (h x y)))
      cases hEdge
      rfl

theorem subgraph_refl (G : Graph V) : Subgraph G G := fun _ _ h => h
theorem subgraph_trans {G H K : Graph V} (h : Subgraph G H) (k : Subgraph H K) :
    Subgraph G K := fun _ _ e => k (h e)
theorem subgraph_antisymm {G H : Graph V} (h : Subgraph G H) (k : Subgraph H G) : G = H :=
  ext (fun _ _ => ⟨fun e => h e, fun e => k e⟩)
theorem empty_subgraph (G : Graph V) : Subgraph empty G := fun _ _ h => False.elim h
theorem subgraph_complete (G : Graph V) : Subgraph G complete := fun _ _ _ => True.intro
theorem edge_union (G H : Graph V) (x y : V) : (union G H).edge x y ↔ G.edge x y ∨ H.edge x y := Iff.rfl
theorem edge_inter (G H : Graph V) (x y : V) : (inter G H).edge x y ↔ G.edge x y ∧ H.edge x y := Iff.rfl
theorem transpose_involutive (G : Graph V) : transpose (transpose G) = G := rfl
theorem union_comm (G H : Graph V) : union G H = union H G := ext (fun _ _ => Or.comm)
theorem inter_comm (G H : Graph V) : inter G H = inter H G := ext (fun _ _ => And.comm)

end Graph
end JonnyLean.GraphTheory
