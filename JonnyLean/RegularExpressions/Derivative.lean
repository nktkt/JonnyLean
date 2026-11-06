import JonnyLean.RegularExpressions.Smart

namespace JonnyLean.RegularExpressions
open JonnyLean.Languages

theorem concat_cons_iff (L K : Language α) (a : α) (w : List α) :
    concat L K (a::w) ↔
      (∃ u v, L (a::u) ∧ K v ∧ u ++ v = w) ∨ (L [] ∧ K (a::w)) := by
  constructor
  · rintro ⟨u,v,hu,hv,e⟩
    cases u with
    | nil => exact .inr ⟨hu, by simpa using e ▸ hv⟩
    | cons b us =>
      cases e
      exact .inl ⟨us,v,hu,hv,rfl⟩
  · rintro (⟨u,v,hu,hv,rfl⟩ | ⟨hu,hv⟩)
    · exact ⟨a::u,v,hu,hv,rfl⟩
    · exact ⟨[],a::w,hu,hv,rfl⟩

theorem star_cons_elim {L : Language α} {x : List α} (h : Star L x) :
    ∀ a w, x = a::w → ∃ u v, L (a::u) ∧ Star L v ∧ u ++ v = w := by
  induction h with
  | nil => intro a w h; cases h
  | @step u v hu hv ih =>
    intro a w h
    cases u with
    | nil => exact ih a w h
    | cons b us => cases h; exact ⟨us,v,hu,hv,rfl⟩

theorem star_cons_iff (L : Language α) (a : α) (w : List α) :
    Star L (a::w) ↔ ∃ u v, L (a::u) ∧ Star L v ∧ u ++ v = w := by
  constructor
  · intro h; exact star_cons_elim h a w rfl
  · rintro ⟨u,v,hu,hv,rfl⟩; exact Star.step hu hv

def derivative [DecidableEq α] (a : α) : Regex α → Regex α
  | .zero => .zero
  | .eps => .zero
  | .atom b => if a = b then .eps else .zero
  | .alt r s => smartAlt (derivative a r) (derivative a s)
  | .seq r s => smartAlt (smartSeq (derivative a r) s)
      (if nullable r then derivative a s else .zero)
  | .star r => smartSeq (derivative a r) (.star r)

theorem derivative_correct [DecidableEq α] (r : Regex α) (a : α) (w : List α) :
    denotes (derivative a r) w ↔ denotes r (a::w) := by
  induction r generalizing w with
  | zero => simp [derivative, denotes, empty]
  | eps => simp [derivative, denotes, empty, epsilon]
  | atom b =>
    by_cases h : a = b
    · subst b; simp [derivative, denotes, epsilon]
    · simp [derivative, denotes, h, empty]
  | alt r s ih jh => simp [derivative, smartAlt_correct, denotes, union, ih, jh]
  | seq r s ih jh =>
    simp only [derivative, smartAlt_correct, smartSeq_correct, denotes, concat_cons_iff]
    by_cases h : nullable r = true
    · have hn := (nullable_correct r).mp h
      simp only [h, ↓reduceIte, jh, hn, true_and]
      apply or_congr
      · unfold concat
        simp only [ih]
      · exact Iff.rfl
    · have hn : ¬ denotes r [] := fun k => h ((nullable_correct r).mpr k)
      simp [h, denotes, empty, hn, concat, ih]
  | star r ih =>
    simp only [derivative, smartSeq_correct, denotes, star_cons_iff]
    unfold concat
    simp only [ih]

theorem derivative_congr [DecidableEq α] {r s : Regex α} (h : Equivalent r s) (a : α) :
    Equivalent (derivative a r) (derivative a s) := by
  intro w
  rw [derivative_correct, derivative_correct]
  exact h (a::w)

end JonnyLean.RegularExpressions
