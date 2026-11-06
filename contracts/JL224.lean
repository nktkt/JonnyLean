import JonnyLean.RegularExpressions.Smart

open JonnyLean.RegularExpressions

theorem contract_JL224 (r : Regex α) : denotes (smartStar r) = JonnyLean.Languages.Star (denotes r) :=
  smartStar_correct r

theorem contract_JL224_definition : smartStar (.zero : Regex Bool) = .eps := rfl

theorem contract_JL224_boundary : smartStar (.star (.atom true : Regex Bool)) = .star (.atom true) := rfl

#print axioms JonnyLean.RegularExpressions.smartStar_correct
#print axioms contract_JL224
