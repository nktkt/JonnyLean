import Std

namespace JonnyLean.Relations

def Compose (r : α → β → Prop) (s : β → γ → Prop) : α → γ → Prop :=
  fun a c => ∃ b, r a b ∧ s b c
def Converse (r : α → β → Prop) : β → α → Prop := fun b a => r a b
def Included (r s : α → β → Prop) : Prop := ∀ a b, r a b → s a b

theorem compose_assoc (r : α → β → Prop) (s : β → γ → Prop) (t : γ → δ → Prop)
    (a : α) (d : δ) : Compose (Compose r s) t a d ↔ Compose r (Compose s t) a d := by
  constructor
  · intro ⟨c, ⟨b, hab, hbc⟩, hcd⟩; exact ⟨b, hab, ⟨c, hbc, hcd⟩⟩
  · intro ⟨b, hab, ⟨c, hbc, hcd⟩⟩; exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩

theorem compose_monotone {r r' : α → β → Prop} {s s' : β → γ → Prop}
    (hr : Included r r') (hs : Included s s') : Included (Compose r s) (Compose r' s') := by
  intro a c ⟨b, hab, hbc⟩; exact ⟨b, hr a b hab, hs b c hbc⟩

theorem converse_compose (r : α → β → Prop) (s : β → γ → Prop) (c : γ) (a : α) :
    Converse (Compose r s) c a ↔ Compose (Converse s) (Converse r) c a := by
  constructor
  · intro ⟨b, hab, hbc⟩; exact ⟨b, hbc, hab⟩
  · intro ⟨b, hbc, hab⟩; exact ⟨b, hab, hbc⟩

theorem compose_equality_left (r : α → β → Prop) (a : α) (b : β) :
    Compose Eq r a b ↔ r a b := by
  constructor
  · intro ⟨x, hax, hxb⟩; exact hax ▸ hxb
  · intro hab; exact ⟨a, rfl, hab⟩

theorem compose_equality_right (r : α → β → Prop) (a : α) (b : β) :
    Compose r Eq a b ↔ r a b := by
  constructor
  · intro ⟨x, hax, hxb⟩; exact hxb ▸ hax
  · intro hab; exact ⟨b, hab, rfl⟩

end JonnyLean.Relations
