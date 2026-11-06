import JonnyLean.Relations.Closure

namespace JonnyLean.Relations

theorem reach_preserves {r : α → α → Prop} {p : α → Prop}
    (step : ∀ a b, p a → r a b → p b) {a b : α}
    (path : Reach r a b) (ha : p a) : p b := by
  induction path with
  | refl => exact ha
  | tail _ edge ih => exact step _ _ ih edge

theorem reach_map {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
    (step : ∀ a b, r a b → s (f a) (f b)) {a b : α}
    (path : Reach r a b) : Reach s (f a) (f b) := by
  induction path with
  | refl => exact .refl _
  | tail _ edge ih => exact .tail ih (step _ _ edge)

theorem reach_simulation {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
    (step : ∀ a b, r a b → Reach s (f a) (f b)) {a b : α}
    (path : Reach r a b) : Reach s (f a) (f b) := by
  induction path with
  | refl => exact .refl _
  | tail _ edge ih => exact reach_trans ih (step _ _ edge)

theorem reach_reverse {r : α → α → Prop} {a b : α} (path : Reach r a b) :
    Reach (Converse r) b a := by
  induction path with
  | refl => exact .refl _
  | tail _ edge ih => exact reach_trans (reach_edge edge) ih

theorem unreachable_of_invariant {r : α → α → Prop} {p : α → Prop}
    (step : ∀ a b, p a → r a b → p b) {a b : α} (ha : p a) (hb : ¬ p b) :
    ¬ Reach r a b := fun path => hb (reach_preserves step path ha)

end JonnyLean.Relations
