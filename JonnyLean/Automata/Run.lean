import JonnyLean.Languages.Basic
namespace JonnyLean.Automata

/-- Deterministic machine; finite-state instances are obtained by choosing finite Q.
The run laws themselves require no finiteness assumption. -/
structure Machine (α : Type u) (Q : Type v) where
  step : Q → α → Q
  start : Q
  accept : Q → Bool

namespace Machine

def run (M : Machine α Q) : Q → List α → Q
  | q, [] => q
  | q, a :: w => M.run (M.step q a) w

@[simp] theorem run_nil (M : Machine α Q) (q : Q) : M.run q [] = q := rfl
@[simp] theorem run_cons (M : Machine α Q) (q : Q) (a : α) (w : List α) :
    M.run q (a :: w) = M.run (M.step q a) w := rfl

theorem run_append (M : Machine α Q) (q : Q) (u v : List α) :
    M.run q (u ++ v) = M.run (M.run q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih => exact ih (M.step q a)

theorem run_singleton (M : Machine α Q) (q : Q) (a : α) : M.run q [a] = M.step q a := rfl

theorem run_replicate_succ (M : Machine α Q) (q : Q) (a : α) (n : Nat) :
    M.run q (List.replicate (n + 1) a) = M.run (M.step q a) (List.replicate n a) := rfl
end Machine
end JonnyLean.Automata
