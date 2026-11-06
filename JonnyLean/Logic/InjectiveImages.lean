import JonnyLean.Logic.Images

namespace JonnyLean.Predicate

theorem image_meet_subset (f : α → β) (p q : α → Prop) :
    Included (image f (meet p q)) (meet (image f p) (image f q)) := by
  intro y ⟨x, hx, hxy⟩; exact ⟨⟨x, hx.1, hxy⟩, ⟨x, hx.2, hxy⟩⟩

theorem image_meet_of_injective (f : α → β) (hf : ∀ a b, f a = f b → a = b)
    (p q : α → Prop) :
    Equivalent (image f (meet p q)) (meet (image f p) (image f q)) := by
  intro y
  constructor
  · exact image_meet_subset f p q y
  · intro ⟨⟨a, ha, hay⟩, ⟨b, hb, hby⟩⟩
    have hab := hf a b (hay.trans hby.symm)
    exact ⟨a, ⟨ha, hab ▸ hb⟩, hay⟩

theorem preimage_image_of_injective (f : α → β) (hf : ∀ a b, f a = f b → a = b)
    (p : α → Prop) : Equivalent (preimage f (image f p)) p := by
  intro x
  constructor
  · intro ⟨a, ha, hax⟩; exact hf a x hax ▸ ha
  · intro hx; exact ⟨x, hx, rfl⟩

theorem image_reflects_inclusion (f : α → β) (hf : ∀ a b, f a = f b → a = b)
    (p q : α → Prop) : Included (image f p) (image f q) ↔ Included p q := by
  constructor
  · intro h x hx
    exact (preimage_image_of_injective f hf q x).mp (h (f x) ⟨x, hx, rfl⟩)
  · exact image_monotone f

theorem image_preimage_of_surjective (f : α → β) (hf : ∀ y, ∃ x, f x = y)
    (q : β → Prop) : Equivalent (image f (preimage f q)) q := by
  intro y
  constructor
  · intro ⟨x, hx, hxy⟩; exact hxy ▸ hx
  · intro hy; obtain ⟨x, hxy⟩ := hf y; exact ⟨x, by change q (f x); rw [hxy]; exact hy, hxy⟩

end JonnyLean.Predicate
