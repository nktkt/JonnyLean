import JonnyLean.Automata.Language
namespace JonnyLean.Automata.Machine

def Stable (M : Machine α Q) (P : Q → Prop) : Prop := ∀ q a, P q → P (M.step q a)

theorem run_invariant (M : Machine α Q) (P : Q → Prop) (stable : M.Stable P)
    (q : Q) (hq : P q) (w : List α) : P (M.run q w) := by
  induction w generalizing q with
  | nil => exact hq
  | cons a w ih => exact ih _ (stable q a hq)

theorem start_invariant (M : Machine α Q) (P : Q → Prop) (stable : M.Stable P)
    (hstart : P M.start) (w : List α) : P (M.run M.start w) := M.run_invariant P stable _ hstart w

theorem rejects_of_invariant (M : Machine α Q) (P : Q → Prop) (stable : M.Stable P)
    (hstart : P M.start) (reject : ∀ q, P q → M.accept q = false) (w : List α) : ¬M.language w := by
  have h := reject _ (M.start_invariant P stable hstart w)
  simp [language, acceptsFrom, h]

theorem stable_inter (M : Machine α Q) {P R : Q → Prop} (hp : M.Stable P) (hr : M.Stable R) :
    M.Stable (fun q => P q ∧ R q) := fun q a h => ⟨hp q a h.1, hr q a h.2⟩
end JonnyLean.Automata.Machine
