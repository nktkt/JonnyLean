import JonnyLean.Combinatorics.Selections

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.Combinatorics

theorem contract_JL057 {α : Type u} {xs ys : List α} {k : Nat} :
    ys ∈ selections k xs ↔ ys.Sublist xs ∧ ys.length = k := mem_selections_iff

example (xs : List α) : selections 0 xs = [[]] := selections_zero xs
example (k : Nat) : selections (k + 1) ([] : List α) = [] := rfl
example (k : Nat) (a : α) (xs : List α) : selections (k + 1) (a :: xs) =
    (selections k xs).map (fun ys => a :: ys) ++ selections (k + 1) xs := rfl
example (xs : List α) : selections xs.length xs = [xs] := selections_full xs
example : selections 2 [1, 2, 3] = [[1, 2], [1, 3], [2, 3]] := rfl
example : selections 2 [1, 1, 1] = [[1, 1], [1, 1], [1, 1]] := rfl
example : selections 4 [1, 2, 3] = [] := rfl

#print axioms JonnyLean.Combinatorics.mem_selections_iff
#print axioms contract_JL057
