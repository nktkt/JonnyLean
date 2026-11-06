import JonnyLean.Polynomials.Translation

open JonnyLean
open JonnyLean.Polynomials

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL093 (c d : Nat) (p : Polynomial) :
    Equivalent (translate c (translate d p)) (translate (c+d) p) :=
  translate_translate c d p

theorem contract_JL093_definition (c : Nat) (p : Polynomial) : translate c p = compose p [c,1] := rfl

theorem contract_JL093_boundary1 : evaluate (translate 0 []) 5 = 0 := by decide

theorem contract_JL093_boundary2 : evaluate (translate 3 [0,0,1]) 2 = 25 := by decide

#print axioms JonnyLean.Polynomials.translate_translate
#print axioms contract_JL093
