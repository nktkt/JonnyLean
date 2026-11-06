import JonnyLean.GraphTheory.Append

namespace JonnyLean.GraphTheory

variable {V : Type u} {G : Graph V} {x y z : V}

/-- Reachability means an actual finite walk exists, including length zero. -/
def Reachable (G : Graph V) (x y : V) : Prop := Nonempty (Walk G x y)

theorem reachable_refl (G : Graph V) (x : V) : Reachable G x x := ⟨.nil x⟩
theorem reachable_of_edge (e : G.edge x y) : Reachable G x y := ⟨.single e⟩
theorem reachable_trans (h : Reachable G x y) (k : Reachable G y z) : Reachable G x z := by
  obtain ⟨p⟩ := h
  obtain ⟨q⟩ := k
  exact ⟨p.append q⟩

theorem reachable_step (e : G.edge x y) (h : Reachable G y z) : Reachable G x z :=
  reachable_trans (reachable_of_edge e) h

/-- The empty-or-first-edge decomposition does not posit a positive length. -/
theorem reachable_iff (G : Graph V) (x z : V) :
    Reachable G x z ↔ x = z ∨ ∃ y, G.edge x y ∧ Reachable G y z := by
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => exact .inl rfl
    | cons e p => exact .inr ⟨_, e, ⟨p⟩⟩
  · intro h
    cases h with
    | inl h => cases h; exact reachable_refl _ _
    | inr h => obtain ⟨y, e, p⟩ := h; exact reachable_step e p

/-- Reachability is contained in every reflexive transitive relation containing the edges. -/
theorem reachable_minimal (R : V → V → Prop)
    (hr : ∀ x, R x x) (ht : ∀ x y z, R x y → R y z → R x z)
    (he : ∀ x y, G.edge x y → R x y) (h : Reachable G x y) : R x y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil x => exact hr x
  | @cons x y z e p ih => exact ht x y z (he x y e) ih

end JonnyLean.GraphTheory
