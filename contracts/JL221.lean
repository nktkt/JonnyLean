import JonnyLean.RegularExpressions.Syntax

open JonnyLean.RegularExpressions

theorem contract_JL221 (r : Regex α) : nullable r = true ↔ denotes r [] :=
  nullable_correct r

theorem contract_JL221_definition (r s : Regex α) : nullable (.seq r s) = (nullable r && nullable s) := rfl

theorem contract_JL221_boundary : nullable (.star (.zero : Regex Bool)) = true := rfl

#print axioms JonnyLean.RegularExpressions.nullable_correct
#print axioms contract_JL221
