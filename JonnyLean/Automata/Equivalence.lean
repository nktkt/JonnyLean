import JonnyLean.Automata.Language
namespace JonnyLean.Automata.Machine

def Equivalent (M : Machine α Q) (q r : Q) : Prop :=
  ∀ w, M.accept (M.run q w) = M.accept (M.run r w)

theorem equivalent_refl (M : Machine α Q) (q : Q) : M.Equivalent q q := fun _ => rfl

theorem equivalent_symm (M : Machine α Q) {q r : Q} (h : M.Equivalent q r) :
    M.Equivalent r q := fun w => (h w).symm

theorem equivalent_trans (M : Machine α Q) {q r s : Q} (h : M.Equivalent q r) (g : M.Equivalent r s) :
    M.Equivalent q s := fun w => (h w).trans (g w)

theorem equivalent_run (M : Machine α Q) {q r : Q} (h : M.Equivalent q r) (u : List α) :
    M.Equivalent (M.run q u) (M.run r u) := by
  intro w
  simpa [M.run_append] using h (u ++ w)

theorem equivalent_step (M : Machine α Q) {q r : Q} (h : M.Equivalent q r) (a : α) :
    M.Equivalent (M.step q a) (M.step r a) := M.equivalent_run h [a]

theorem equivalent_accepts (M : Machine α Q) {q r : Q} (h : M.Equivalent q r) (w : List α) :
    M.acceptsFrom q w ↔ M.acceptsFrom r w := by unfold acceptsFrom; rw [h w]
end JonnyLean.Automata.Machine
