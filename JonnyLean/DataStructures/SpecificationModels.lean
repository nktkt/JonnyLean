import JonnyLean.DataStructures.Persistent

/-! Fixed independent mathematical models and checked bridges for the task contracts. -/

namespace JonnyLean.VerifiedPrograms.Specification

def queueView (q : DataStructures.Queue α) : List α := q.front ++ q.back.reverse

def lookup (key : Nat) : List (Nat × α) → Option α
  | [] => none
  | (k, v) :: rest => if k = key then some v else lookup key rest

theorem queueView_matches (q : DataStructures.Queue α) : queueView q = q.contents := rfl

theorem lookup_matches (key : Nat) (m : List (Nat × α)) : lookup key m = DataStructures.Assoc.lookup key m := by
  induction m with
  | nil => rfl
  | cons pair rest ih => rcases pair with ⟨k, v⟩; simp only [lookup, DataStructures.Assoc.lookup, ih, eq_comm]

end JonnyLean.VerifiedPrograms.Specification
