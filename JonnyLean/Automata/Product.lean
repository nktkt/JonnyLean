import JonnyLean.Automata.Language
namespace JonnyLean.Automata.Machine

def product (M : Machine α Q) (N : Machine α R) : Machine α (Q × R) where
  step q a := (M.step q.1 a, N.step q.2 a)
  start := (M.start, N.start)
  accept q := M.accept q.1 && N.accept q.2

theorem run_product (M : Machine α Q) (N : Machine α R) (q : Q) (r : R) (w : List α) :
    (M.product N).run (q, r) w = (M.run q w, N.run r w) := by
  induction w generalizing q r with
  | nil => rfl
  | cons a w ih => exact ih (M.step q a) (N.step r a)

theorem accepts_product (M : Machine α Q) (N : Machine α R) (w : List α) :
    (M.product N).language w ↔ M.language w ∧ N.language w := by
  change ((M.accept ((M.product N).run (M.start, N.start) w).1 &&
    N.accept ((M.product N).run (M.start, N.start) w).2) = true) ↔ _
  rw [run_product]
  simp [language, acceptsFrom]

theorem language_product (M : Machine α Q) (N : Machine α R) :
    (M.product N).language = Languages.inter M.language N.language := by
  funext w; exact propext (accepts_product M N w)

theorem product_start (M : Machine α Q) (N : Machine α R) :
    (M.product N).start = (M.start, N.start) := rfl
end JonnyLean.Automata.Machine
