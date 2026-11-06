import JonnyLean.Relations.Composition

namespace JonnyLean.Relations

/-- A finite path, including a path with zero edges. -/
inductive Reach (r : α → α → Prop) : α → α → Prop where
  | refl (a) : Reach r a a
  | tail {a b c} : Reach r a b → r b c → Reach r a c

theorem reach_edge {r : α → α → Prop} {a b : α} (h : r a b) : Reach r a b :=
  .tail (.refl a) h

theorem reach_trans {r : α → α → Prop} {a b c : α}
    (hab : Reach r a b) (hbc : Reach r b c) : Reach r a c := by
  induction hbc with
  | refl => exact hab
  | tail _ edge ih => exact .tail ih edge

theorem reach_least {r s : α → α → Prop} (hinc : Included r s)
    (href : ∀ a, s a a) (htrans : ∀ a b c, s a b → s b c → s a c) :
    Included (Reach r) s := by
  intro a b h
  induction h with
  | refl => exact href _
  | tail _ edge ih => exact htrans _ _ _ ih (hinc _ _ edge)

theorem reach_monotone {r s : α → α → Prop} (h : Included r s) :
    Included (Reach r) (Reach s) := by
  apply reach_least
  · exact fun a b hab => reach_edge (h a b hab)
  · exact Reach.refl
  · exact fun _ _ _ hab hbc => reach_trans hab hbc

theorem reach_idempotent (r : α → α → Prop) (a b : α) :
    Reach (Reach r) a b ↔ Reach r a b := by
  constructor
  · exact reach_least (fun _ _ h => h) Reach.refl (fun _ _ _ => reach_trans) a b
  · exact reach_edge

end JonnyLean.Relations
