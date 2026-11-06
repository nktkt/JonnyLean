import JonnyLean.RegularExpressions.Transformations

open JonnyLean.RegularExpressions

theorem contract_JL232 (r : Regex α) (w : List α) : denotes (.star r) w ↔ w = [] ∨ ∃ u v, denotes r u ∧ denotes (.star r) v ∧ u ++ v = w :=
  star_unfold r w

theorem contract_JL232_definition (r : Regex α) : denotes (.star r) = JonnyLean.Languages.Star (denotes r) := rfl

theorem contract_JL232_boundary : accepts (.star (.zero : Regex Bool)) [true] = false := by decide

#print axioms JonnyLean.RegularExpressions.star_unfold
#print axioms contract_JL232
