import JonnyLean.Logic.Predicates

namespace JonnyLean.Predicate

def image (f : α → β) (p : α → Prop) : β → Prop := fun y => ∃ x, p x ∧ f x = y
def preimage (f : α → β) (q : β → Prop) : α → Prop := fun x => q (f x)

theorem image_preimage_adjunction (f : α → β) (p : α → Prop) (q : β → Prop) :
    Included (image f p) q ↔ Included p (preimage f q) := by
  constructor
  · intro h x hx; exact h (f x) ⟨x, hx, rfl⟩
  · intro h y ⟨x, hx, hxy⟩; exact hxy ▸ h x hx

theorem image_monotone (f : α → β) {p q : α → Prop} (h : Included p q) :
    Included (image f p) (image f q) := by
  intro y ⟨x, hx, hxy⟩; exact ⟨x, h x hx, hxy⟩

theorem image_join (f : α → β) (p q : α → Prop) :
    Equivalent (image f (join p q)) (join (image f p) (image f q)) := by
  intro y
  constructor
  · intro ⟨x, hx, hxy⟩
    exact hx.elim (fun hp => Or.inl ⟨x, hp, hxy⟩) (fun hq => Or.inr ⟨x, hq, hxy⟩)
  · intro h
    cases h with
    | inl h => obtain ⟨x, hp, hxy⟩ := h; exact ⟨x, Or.inl hp, hxy⟩
    | inr h => obtain ⟨x, hq, hxy⟩ := h; exact ⟨x, Or.inr hq, hxy⟩

theorem image_comp (f : α → β) (g : β → γ) (p : α → Prop) :
    Equivalent (image (g ∘ f) p) (image g (image f p)) := by
  intro z
  constructor
  · intro ⟨x, hx, hz⟩; exact ⟨f x, ⟨x, hx, rfl⟩, hz⟩
  · intro ⟨y, ⟨x, hx, hxy⟩, hyz⟩; exact ⟨x, hx, by simp [hxy, hyz]⟩

theorem preimage_meet (f : α → β) (p q : β → Prop) :
    Equivalent (preimage f (meet p q)) (meet (preimage f p) (preimage f q)) :=
  fun _ => Iff.rfl

end JonnyLean.Predicate
