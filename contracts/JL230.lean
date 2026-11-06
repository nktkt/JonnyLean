import JonnyLean.RegularExpressions.Transformations

open JonnyLean.RegularExpressions

theorem contract_JL230 (r : Regex α) (w : List α) : denotes (reversed r) w ↔ denotes r w.reverse :=
  reversed_correct r w

theorem contract_JL230_definition (r s : Regex α) : reversed (.seq r s) = .seq (reversed s) (reversed r) := rfl

theorem contract_JL230_boundary : accepts (reversed (.seq (.atom true) (.atom false)) : Regex Bool) [false,true] = true := by decide

#print axioms JonnyLean.RegularExpressions.reversed_correct
#print axioms contract_JL230
