import Init.Data.List.Lemmas

namespace JonnyLean.Languages

abbrev Language (α : Type u) := List α → Prop

def Included (L K : Language α) : Prop := ∀ w, L w → K w
def empty : Language α := fun _ => False
def epsilon : Language α := fun w => w = []
def union (L K : Language α) : Language α := fun w => L w ∨ K w
def inter (L K : Language α) : Language α := fun w => L w ∧ K w

theorem included_refl (L : Language α) : Included L L := fun _ h => h
theorem included_trans {L K M : Language α} (h : Included L K) (g : Included K M) :
    Included L M := fun w hw => g w (h w hw)
theorem included_antisymm {L K : Language α} (h : Included L K) (g : Included K L) : L = K := by
  funext w
  exact propext ⟨h w, g w⟩
theorem empty_included (L : Language α) : Included empty L := fun _ h => h.elim

theorem union_included {L K M : Language α} :
    Included (union L K) M ↔ Included L M ∧ Included K M := by
  constructor
  · intro h; exact ⟨fun w hw => h w (.inl hw), fun w hw => h w (.inr hw)⟩
  · intro h w hw; exact hw.elim (h.1 w) (h.2 w)

end JonnyLean.Languages
