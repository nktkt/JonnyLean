import JonnyLean.RegularExpressions.Smart

open JonnyLean.RegularExpressions

theorem contract_JL223 (r s : Regex α) : denotes (smartSeq r s) = JonnyLean.Languages.concat (denotes r) (denotes s) :=
  smartSeq_correct r s

theorem contract_JL223_definition (r : Regex α) : smartSeq .zero r = .zero := rfl

theorem contract_JL223_boundary : smartSeq (.eps : Regex Bool) (.atom true) = .atom true := rfl

#print axioms JonnyLean.RegularExpressions.smartSeq_correct
#print axioms contract_JL223
