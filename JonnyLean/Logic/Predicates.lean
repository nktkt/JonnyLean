import Std

namespace JonnyLean.Predicate

def Included (p q : α → Prop) : Prop := ∀ x, p x → q x
def Equivalent (p q : α → Prop) : Prop := ∀ x, p x ↔ q x
def meet (p q : α → Prop) : α → Prop := fun x => p x ∧ q x
def join (p q : α → Prop) : α → Prop := fun x => p x ∨ q x
def complement (p : α → Prop) : α → Prop := fun x => ¬ p x

theorem included_trans {p q r : α → Prop} (hpq : Included p q)
    (hqr : Included q r) : Included p r := fun x hx => hqr x (hpq x hx)

theorem meet_greatest {p q r : α → Prop} :
    Included r (meet p q) ↔ Included r p ∧ Included r q := by
  constructor
  · intro h; exact ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩
  · intro h x hx; exact ⟨h.1 x hx, h.2 x hx⟩

theorem join_least {p q r : α → Prop} :
    Included (join p q) r ↔ Included p r ∧ Included q r := by
  constructor
  · intro h; exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
  · intro h x hx; exact hx.elim (h.1 x) (h.2 x)

theorem meet_join_distrib (p q r : α → Prop) :
    Equivalent (meet p (join q r)) (join (meet p q) (meet p r)) := by
  intro x
  constructor
  · intro ⟨hp, hqr⟩; exact hqr.elim (fun hq => Or.inl ⟨hp, hq⟩) (fun hr => Or.inr ⟨hp, hr⟩)
  · intro h; exact h.elim (fun h => ⟨h.1, Or.inl h.2⟩) (fun h => ⟨h.1, Or.inr h.2⟩)

theorem complement_join (p q : α → Prop) :
    Equivalent (complement (join p q)) (meet (complement p) (complement q)) := by
  intro x
  constructor
  · intro h; exact ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩
  · intro h hpq; exact hpq.elim h.1 h.2

theorem complement_antitone {p q : α → Prop} (h : Included p q) :
    Included (complement q) (complement p) := fun x hn hp => hn (h x hp)

end JonnyLean.Predicate
