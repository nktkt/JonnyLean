import JonnyLean.Automata.Language
namespace JonnyLean.Automata.Machine

def complement (M : Machine α Q) : Machine α Q := { M with accept := fun q => !M.accept q }

theorem run_complement (M : Machine α Q) (q : Q) (w : List α) : M.complement.run q w = M.run q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih => exact ih (M.step q a)

theorem language_complement (M : Machine α Q) (w : List α) :
    M.complement.language w ↔ ¬M.language w := by
  change (Bool.not (M.accept (M.complement.run M.start w)) = true) ↔ ¬(M.accept (M.run M.start w) = true)
  rw [run_complement]
  cases M.accept (M.run M.start w) <;> simp

theorem complement_complement (M : Machine α Q) : M.complement.complement = M := by
  cases M
  simp [complement]

theorem excluded_acceptance (M : Machine α Q) (w : List α) : M.language w ∨ M.complement.language w := by
  rw [language_complement]
  unfold language acceptsFrom
  cases M.accept (M.run M.start w) <;> simp
end JonnyLean.Automata.Machine
