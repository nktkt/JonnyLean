import JonnyLean.RegularExpressions.Matcher

open JonnyLean.RegularExpressions

theorem contract_JL229 [DecidableEq α] {r s : Regex α} (h : ∀ w, denotes r w ↔ denotes s w) (u : List α) : ∀ v, denotes (derivatives u r) v ↔ denotes (derivatives u s) v :=
  derivatives_congr h u

theorem contract_JL229_definition (r s : Regex α) : Equivalent r s = (∀ w, denotes r w ↔ denotes s w) := rfl

theorem contract_JL229_boundary : accepts (.alt (.zero : Regex Bool) (.atom true)) [true] = accepts (.atom true : Regex Bool) [true] := by decide

#print axioms JonnyLean.RegularExpressions.derivatives_congr
#print axioms contract_JL229
