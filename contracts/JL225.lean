import JonnyLean.RegularExpressions.Derivative

open JonnyLean.RegularExpressions

theorem contract_JL225 [DecidableEq α] (r : Regex α) (a : α) (w : List α) : denotes (derivative a r) w ↔ denotes r (a::w) :=
  derivative_correct r a w

theorem contract_JL225_definition [DecidableEq α] (a b : α) : derivative a (.atom b) = (if a = b then .eps else .zero) := rfl

theorem contract_JL225_boundary : derivative true (.eps : Regex Bool) = .zero := rfl

#print axioms JonnyLean.RegularExpressions.derivative_correct
#print axioms contract_JL225
