import JonnyLean.Automata.Run
import JonnyLean.Languages.Quotient
namespace JonnyLean.Automata.Machine

def acceptsFrom (M : Machine α Q) (q : Q) : Languages.Language α :=
  fun w => M.accept (M.run q w) = true

def language (M : Machine α Q) : Languages.Language α := M.acceptsFrom M.start

def restart (M : Machine α Q) (q : Q) : Machine α Q := { M with start := q }

theorem acceptsFrom_nil (M : Machine α Q) (q : Q) : M.acceptsFrom q [] ↔ M.accept q = true := Iff.rfl

theorem acceptsFrom_append (M : Machine α Q) (q : Q) (u v : List α) :
    M.acceptsFrom q (u ++ v) ↔ M.acceptsFrom (M.run q u) v := by
  simp [acceptsFrom, run_append]

theorem run_restart (M : Machine α Q) (p q : Q) (w : List α) : (M.restart p).run q w = M.run q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih => exact ih (M.step q a)

theorem language_residual (M : Machine α Q) (u : List α) :
    Languages.leftQuotient u M.language = (M.restart (M.run M.start u)).language := by
  funext w
  change (M.accept (M.run M.start (u ++ w)) = true) =
    (M.accept ((M.restart (M.run M.start u)).run (M.run M.start u) w) = true)
  rw [run_append, run_restart]
end JonnyLean.Automata.Machine
