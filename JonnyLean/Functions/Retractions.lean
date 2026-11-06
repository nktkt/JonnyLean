import JonnyLean.Functions.Inverses

namespace JonnyLean.Functions

def Idempotent (p : α → α) : Prop := ∀ x, p (p x) = p x
def Fixed (p : α → α) (x : α) : Prop := p x = x

theorem retraction_idempotent {s : β → α} {r : α → β} (h : LeftInverse r s) :
    Idempotent (s ∘ r) := by
  intro x; simp [h (r x)]

theorem fixed_iff_in_image {p : α → α} (hp : Idempotent p) (x : α) :
    Fixed p x ↔ ∃ y, p y = x := by
  constructor
  · intro h; exact ⟨x, h⟩
  · intro ⟨y, hy⟩; subst x; exact hp y

theorem injective_idempotent_is_identity {p : α → α} (hp : Idempotent p)
    (hi : Injective p) : ∀ x, p x = x := fun x => hi (p x) x (hp x)

theorem surjective_idempotent_is_identity {p : α → α} (hp : Idempotent p)
    (hs : Surjective p) : ∀ x, p x = x := by
  intro x; obtain ⟨y, rfl⟩ := hs x; exact hp y

theorem commuting_idempotents {p q : α → α} (hp : Idempotent p) (hq : Idempotent q)
    (hc : ∀ x, p (q x) = q (p x)) : Idempotent (p ∘ q) := by
  intro x
  change p (q (p (q x))) = p (q x)
  rw [← hc (q x), hq x, hp (q x)]

end JonnyLean.Functions
