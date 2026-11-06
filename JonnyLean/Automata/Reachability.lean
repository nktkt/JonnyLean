import JonnyLean.Automata.Invariants
namespace JonnyLean.Automata.Machine

def Reachable (M : Machine α Q) (q : Q) : Prop := ∃ w, M.run M.start w = q

theorem reachable_start (M : Machine α Q) : M.Reachable M.start := ⟨[], rfl⟩

theorem reachable_step (M : Machine α Q) : M.Stable M.Reachable := by
  rintro q a ⟨w, rfl⟩
  exact ⟨w ++ [a], by rw [M.run_append]; rfl⟩

theorem reachable_run (M : Machine α Q) {q : Q} (hq : M.Reachable q) (w : List α) :
    M.Reachable (M.run q w) := M.run_invariant _ M.reachable_step q hq w

theorem reachable_minimal (M : Machine α Q) (P : Q → Prop) (stable : M.Stable P)
    (hstart : P M.start) : ∀ q, M.Reachable q → P q := by
  rintro q ⟨w, rfl⟩
  exact M.start_invariant P stable hstart w

theorem reachable_accept (M : Machine α Q) (w : List α) (hw : M.language w) :
    ∃ q, M.Reachable q ∧ M.accept q = true := ⟨M.run M.start w, ⟨w, rfl⟩, hw⟩
end JonnyLean.Automata.Machine
