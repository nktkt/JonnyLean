import JonnyLean.Automata.Language
namespace JonnyLean.Automata.Machine

def comap (M : Machine β Q) (f : α → β) : Machine α Q where
  step q a := M.step q (f a)
  start := M.start
  accept := M.accept

theorem run_comap (M : Machine β Q) (f : α → β) (q : Q) (w : List α) :
    (M.comap f).run q w = M.run q (w.map f) := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih => exact ih (M.step q (f a))

theorem language_comap (M : Machine β Q) (f : α → β) (w : List α) :
    (M.comap f).language w ↔ M.language (w.map f) := by
  change (M.accept ((M.comap f).run M.start w) = true) ↔ _
  rw [run_comap]
  rfl

theorem comap_id (M : Machine α Q) : M.comap id = M := by cases M; rfl

theorem comap_comp (M : Machine γ Q) (f : α → β) (g : β → γ) :
    (M.comap g).comap f = M.comap (fun a => g (f a)) := rfl
end JonnyLean.Automata.Machine
