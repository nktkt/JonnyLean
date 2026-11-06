import JonnyLean.RegularExpressions.Transformations

open JonnyLean.RegularExpressions

theorem contract_JL231 (u w : List α) : denotes (literal u) w ↔ w = u :=
  literal_correct u w

theorem contract_JL231_definition (a : α) (w : List α) : literal (a::w) = .seq (.atom a) (literal w) := rfl

theorem contract_JL231_boundary : accepts (literal [true,false,true]) [true,false] = false := by decide

#print axioms JonnyLean.RegularExpressions.literal_correct
#print axioms contract_JL231
