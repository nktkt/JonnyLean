import Std

namespace JonnyLean.Relations

def Kernel (f : α → β) : α → α → Prop := fun a b => f a = f b

theorem kernel_reflexive (f : α → β) (a : α) : Kernel f a a := rfl

theorem kernel_symmetric (f : α → β) {a b : α} (h : Kernel f a b) : Kernel f b a := h.symm

theorem kernel_transitive (f : α → β) {a b c : α}
    (hab : Kernel f a b) (hbc : Kernel f b c) : Kernel f a c := hab.trans hbc

theorem kernel_comp_coarsens (f : α → β) (g : β → γ) {a b : α}
    (h : Kernel f a b) : Kernel (g ∘ f) a b := congrArg g h

theorem kernel_comp_of_injective (f : α → β) (g : β → γ)
    (hg : ∀ x y, g x = g y → x = y) (a b : α) :
    Kernel (g ∘ f) a b ↔ Kernel f a b :=
  ⟨hg (f a) (f b), kernel_comp_coarsens f g⟩

/-- A map constant on the fibers of `f` factors through `f` when an explicit
section is supplied. No section is selected from a mere surjectivity proof. -/
theorem factor_with_section (f : α → β) (s : β → α) (hs : ∀ b, f (s b) = b)
    (g : α → γ) (hg : ∀ a a', f a = f a' → g a = g a') :
    ∀ a, (g ∘ s) (f a) = g a := by
  intro a; exact hg (s (f a)) a (hs (f a))

theorem factor_unique (f : α → β) (hf : ∀ b, ∃ a, f a = b) (g h : β → γ)
    (he : ∀ a, g (f a) = h (f a)) : ∀ b, g b = h b := by
  intro b; obtain ⟨a, rfl⟩ := hf b; exact he a

end JonnyLean.Relations
