import JonnyLean.RegularExpressions.Matcher
import JonnyLean.Languages.Reversal

namespace JonnyLean.RegularExpressions
open JonnyLean.Languages

def reversed : Regex α → Regex α
  | .zero => .zero
  | .eps => .eps
  | .atom a => .atom a
  | .alt r s => .alt (reversed r) (reversed s)
  | .seq r s => .seq (reversed s) (reversed r)
  | .star r => .star (reversed r)

theorem star_reverse_iff (L : Language α) (w : List α) :
    Star (fun u => L u.reverse) w ↔ Star L w.reverse := by
  have forward : ∀ (K : Language α) (v : List α), Star (fun u => K u.reverse) v → Star K v.reverse := by
    intro K v h
    induction h with
    | nil => exact .nil
    | @step u v hu hv ih =>
      rw [List.reverse_append]
      exact star_append ih (star_single hu)
  constructor
  · exact forward L w
  · intro h
    have h' : Star (fun u => (fun v => L v.reverse) u.reverse) w.reverse := by simpa using h
    simpa using forward (fun u => L u.reverse) w.reverse h'

theorem reversed_correct (r : Regex α) (w : List α) :
    denotes (reversed r) w ↔ denotes r w.reverse := by
  induction r generalizing w with
  | zero => rfl
  | eps => simp [reversed, denotes, epsilon]
  | atom a => simp [reversed, denotes, List.reverse_eq_iff]
  | alt r s ih jh => simp [reversed, denotes, union, ih, jh]
  | seq r s ih jh =>
    have hr : denotes (reversed r) = reverse (denotes r) := funext fun v => propext (ih v)
    have hs : denotes (reversed s) = reverse (denotes s) := funext fun v => propext (jh v)
    simp only [reversed, denotes, hr, hs, ← reverse_concat]
    rfl
  | star r ih =>
    have hr : denotes (reversed r) = fun v => denotes r v.reverse := funext fun v => propext (ih v)
    simp only [reversed, denotes, hr, star_reverse_iff]

theorem reversed_involution (r : Regex α) : reversed (reversed r) = r := by
  induction r <;> simp [reversed, *]

def literal : List α → Regex α
  | [] => .eps
  | a::w => .seq (.atom a) (literal w)

theorem literal_correct (u w : List α) : denotes (literal u) w ↔ w = u := by
  induction u generalizing w with
  | nil => rfl
  | cons a u ih =>
    simp only [literal, denotes, concat, ih]
    constructor
    · rintro ⟨x,y,hx,hy,e⟩; simpa [hx,hy] using e.symm
    · intro h; subst w; exact ⟨[a],u,rfl,rfl,rfl⟩

theorem literal_append (u v : List α) : Equivalent (literal (u ++ v)) (.seq (literal u) (literal v)) := by
  intro w
  simp only [literal_correct, denotes, concat]
  constructor
  · intro h; exact ⟨u,v,rfl,rfl,h.symm⟩
  · rintro ⟨x,y,hx,hy,e⟩
    simpa [hx,hy] using e.symm

theorem star_unfold (r : Regex α) (w : List α) :
    denotes (.star r) w ↔ w = [] ∨
      ∃ u v, denotes r u ∧ denotes (.star r) v ∧ u ++ v = w := by
  constructor
  · intro h
    cases h with
    | nil => exact .inl rfl
    | @step u v hu hv => exact .inr ⟨u,v,hu,hv,rfl⟩
  · rintro (rfl | ⟨u,v,hu,hv,rfl⟩)
    · exact Star.nil
    · exact Star.step hu hv

end JonnyLean.RegularExpressions
