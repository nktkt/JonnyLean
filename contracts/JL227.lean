import JonnyLean.RegularExpressions.Matcher

open JonnyLean.RegularExpressions

theorem contract_JL227 [DecidableEq α] (r : Regex α) (w : List α) : accepts r w = true ↔ denotes r w :=
  accepts_correct r w

theorem contract_JL227_definition [DecidableEq α] (r : Regex α) (w : List α) : accepts r w = nullable (derivatives w r) := rfl

theorem contract_JL227_boundary : accepts (.star (.alt (.atom true) (.atom false)) : Regex Bool) [true,false,true] = true := by decide

#print axioms JonnyLean.RegularExpressions.accepts_correct
#print axioms contract_JL227
