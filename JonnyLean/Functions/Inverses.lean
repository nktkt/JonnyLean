import JonnyLean.Functions.Composition

namespace JonnyLean.Functions

def LeftInverse (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x
def RightInverse (g : β → α) (f : α → β) : Prop := ∀ y, f (g y) = y

theorem injective_of_left_inverse {f : α → β} {g : β → α} (h : LeftInverse g f) :
    Injective f := by
  intro a b hab
  calc a = g (f a) := (h a).symm
       _ = g (f b) := congrArg g hab
       _ = b := h b

theorem surjective_of_right_inverse {f : α → β} {g : β → α} (h : RightInverse g f) :
    Surjective f := fun y => ⟨g y, h y⟩

theorem inverses_agree {f : α → β} {g h : β → α}
    (hg : LeftInverse g f) (hh : RightInverse h f) : ∀ y, g y = h y := by
  intro y
  calc g y = g (f (h y)) := congrArg g (hh y).symm
       _ = h y := hg (h y)

theorem left_inverse_comp {f : α → β} {g : β → γ} {f' : β → α} {g' : γ → β}
    (hf : LeftInverse f' f) (hg : LeftInverse g' g) :
    LeftInverse (f' ∘ g') (g ∘ f) := by
  intro x; simp [hg (f x), hf x]

theorem right_inverse_of_injective {f : α → β} {g : β → α}
    (hg : Injective g) (h : LeftInverse g f) : RightInverse g f := by
  intro y; apply hg; exact h (g y)

theorem left_inverse_of_injective {f : α → β} {g : β → α}
    (hf : Injective f) (h : RightInverse g f) : LeftInverse g f := by
  intro x; apply hf; exact h (f x)

end JonnyLean.Functions
