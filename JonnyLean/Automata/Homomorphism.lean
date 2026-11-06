import JonnyLean.Automata.Language
namespace JonnyLean.Automata

structure Hom (M : Machine α Q) (N : Machine α R) where
  state : Q → R
  start : state M.start = N.start
  step : ∀ q a, state (M.step q a) = N.step (state q) a
  accept : ∀ q, N.accept (state q) = M.accept q

namespace Hom

theorem map_run {M : Machine α Q} {N : Machine α R} (f : Hom M N) (q : Q) (w : List α) :
    f.state (M.run q w) = N.run (f.state q) w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih => simpa [Machine.run, f.step] using ih (M.step q a)

theorem language_eq {M : Machine α Q} {N : Machine α R} (f : Hom M N) : M.language = N.language := by
  funext w
  unfold Machine.language Machine.acceptsFrom
  rw [← f.start, ← f.map_run, f.accept]

def id (M : Machine α Q) : Hom M M where
  state := fun q => q
  start := rfl
  step := fun _ _ => rfl
  accept := fun _ => rfl

def comp {M : Machine α Q} {N : Machine α R} {P : Machine α S} (g : Hom N P) (f : Hom M N) : Hom M P where
  state := fun q => g.state (f.state q)
  start := by rw [f.start, g.start]
  step := by intro q a; rw [f.step, g.step]
  accept := by intro q; rw [g.accept, f.accept]

theorem comp_state {M : Machine α Q} {N : Machine α R} {P : Machine α S}
    (g : Hom N P) (f : Hom M N) (q : Q) : (g.comp f).state q = g.state (f.state q) := rfl
end Hom
end JonnyLean.Automata
