import JonnyLean.RegularExpressions.Smart

open JonnyLean.RegularExpressions

theorem contract_JL222 (r s : Regex α) (w : List α) : denotes (smartAlt r s) w ↔ denotes r w ∨ denotes s w :=
  smartAlt_correct r s w

theorem contract_JL222_definition (s : Regex α) : smartAlt .zero s = s := rfl

theorem contract_JL222_boundary : smartAlt (.zero : Regex Bool) .eps = .eps := rfl

#print axioms JonnyLean.RegularExpressions.smartAlt_correct
#print axioms contract_JL222
