import JonnyLean.DiscreteProbability.Distribution

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.DiscreteProbability

theorem contract_JL060 {α : Type u} (d : Distribution α) (p : α → Bool) :
    (d.probability p).numerator + (d.probability (fun a => !p a)).numerator =
      mass d.weight d.outcomes := Distribution.probability_complement d p

example (d : Distribution α) (p : α → Bool) :
    (d.probability p).numerator = eventMass d.weight p d.outcomes := rfl
example (d : Distribution α) (p : α → Bool) :
    (d.probability p).denominator = mass d.weight d.outcomes := rfl
example (d : Distribution α) (p : α → Bool) : 0 < (d.probability p).denominator :=
  (d.probability p).positive
example (d : Distribution α) (p : α → Bool) :
    (d.probability p).numerator ≤ (d.probability p).denominator := (d.probability p).bounded
example : ((Distribution.uniform [false, true] (by decide)).probability id).numerator = 1 := rfl
example : ((Distribution.uniform [false, true] (by decide)).probability id).denominator = 2 := rfl
example (d : Distribution α) : d.outcomes ≠ [] := Distribution.outcomes_nonempty d

#print axioms JonnyLean.DiscreteProbability.Distribution.probability_complement
#print axioms contract_JL060
