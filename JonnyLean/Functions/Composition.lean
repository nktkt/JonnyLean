import Std

namespace JonnyLean.Functions

def Injective (f : α → β) : Prop := ∀ a b, f a = f b → a = b
def Surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b
def Bijective (f : α → β) : Prop := Injective f ∧ Surjective f

theorem injective_comp {f : α → β} {g : β → γ} (hf : Injective f) (hg : Injective g) :
    Injective (g ∘ f) := fun a b h => hf a b (hg (f a) (f b) h)

theorem surjective_comp {f : α → β} {g : β → γ} (hf : Surjective f) (hg : Surjective g) :
    Surjective (g ∘ f) := by
  intro c; obtain ⟨b, hb⟩ := hg c; obtain ⟨a, ha⟩ := hf b
  exact ⟨a, by simp [ha, hb]⟩

theorem injective_of_comp {f : α → β} {g : β → γ} (h : Injective (g ∘ f)) :
    Injective f := fun a b hab => h a b (congrArg g hab)

theorem surjective_of_comp {f : α → β} {g : β → γ} (h : Surjective (g ∘ f)) :
    Surjective g := by
  intro c; obtain ⟨a, ha⟩ := h c; exact ⟨f a, ha⟩

theorem bijective_comp {f : α → β} {g : β → γ} (hf : Bijective f) (hg : Bijective g) :
    Bijective (g ∘ f) := ⟨injective_comp hf.1 hg.1, surjective_comp hf.2 hg.2⟩

theorem cancel_right {f g : β → γ} {h : α → β} (hh : Surjective h)
    (he : ∀ x, f (h x) = g (h x)) : ∀ y, f y = g y := by
  intro y; obtain ⟨x, rfl⟩ := hh y; exact he x

end JonnyLean.Functions
