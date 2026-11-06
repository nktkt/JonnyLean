import JonnyLean.RegularExpressions.Matcher

open JonnyLean.RegularExpressions

theorem contract_JL228 [DecidableEq α] (r : Regex α) (u v : List α) : accepts r (u ++ v) = accepts (derivatives u r) v :=
  accepts_append r u v

theorem contract_JL228_definition [DecidableEq α] (r : Regex α) (a : α) (w : List α) : derivatives (a::w) r = derivatives w (derivative a r) := rfl

theorem contract_JL228_boundary : accepts (.seq (.atom true) (.atom false) : Regex Bool) [true] = false := by decide

#print axioms JonnyLean.RegularExpressions.accepts_append
#print axioms contract_JL228
