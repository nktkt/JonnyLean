import JonnyLean.Imperative.Hoare

namespace JonnyLean.Imperative

def spin : Cmd := .while (.truth true) .skip

theorem spin_exhausts (n : Nat) (s : State) : run n spin s = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (run n .skip s).bind (run n spin) = none
    cases n with
    | zero => rfl
    | succ n => exact ih

theorem spin_diverges (s t : State) : ¬Exec spin s t := by
  intro h
  obtain ⟨n, hn⟩ := run_complete h
  rw [spin_exhausts] at hn
  contradiction

theorem spin_partial_correct (P Q : Assertion) : Hoare P spin Q := by
  intro s t _ h
  exact False.elim (spin_diverges s t h)

end JonnyLean.Imperative
