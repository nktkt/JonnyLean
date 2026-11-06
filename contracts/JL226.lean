import JonnyLean.RegularExpressions.Matcher

open JonnyLean.RegularExpressions

theorem contract_JL226 [DecidableEq α] (u v : List α) (r : Regex α) : denotes (derivatives u r) v ↔ denotes r (u ++ v) :=
  derivatives_correct u v r

theorem contract_JL226_definition [DecidableEq α] (r : Regex α) : derivatives [] r = r := rfl

theorem contract_JL226_boundary : derivatives [true,false] (.seq (.atom true) (.atom false) : Regex Bool) = .eps := by decide

#print axioms JonnyLean.RegularExpressions.derivatives_correct
#print axioms contract_JL226
