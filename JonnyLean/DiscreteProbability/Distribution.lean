import JonnyLean.DiscreteProbability.Mass

namespace JonnyLean.DiscreteProbability

/-- An unreduced fraction n/d in [0,1]. Its denominator is explicitly positive;
we do not identify different fraction representations by structure equality. -/
structure Probability where
  numerator : Nat
  denominator : Nat
  positive : 0 < denominator
  bounded : numerator ≤ denominator

/-- A finite counting distribution with natural weights and nonzero total mass. -/
structure Distribution (α : Type u) where
  outcomes : List α
  weight : α → Nat
  positive : 0 < mass weight outcomes

namespace Distribution

def total (d : Distribution α) : Nat := mass d.weight d.outcomes

def probability (d : Distribution α) (event : α → Bool) : Probability where
  numerator := eventMass d.weight event d.outcomes
  denominator := d.total
  positive := d.positive
  bounded := eventMass_le d.weight event d.outcomes

@[simp] theorem probability_numerator (d : Distribution α) (p : α → Bool) :
    (d.probability p).numerator = eventMass d.weight p d.outcomes := rfl
@[simp] theorem probability_denominator (d : Distribution α) (p : α → Bool) :
    (d.probability p).denominator = d.total := rfl

theorem total_positive (d : Distribution α) : 0 < d.total := d.positive

theorem probability_empty (d : Distribution α) : (d.probability (fun _ => false)).numerator = 0 :=
  eventMass_false _ _

theorem probability_universal (d : Distribution α) :
    (d.probability (fun _ => true)).numerator = (d.probability (fun _ => true)).denominator :=
  eventMass_true _ _

/-- Complementary probabilities have numerators summing to the common denominator. -/
theorem probability_complement (d : Distribution α) (p : α → Bool) :
    (d.probability p).numerator + (d.probability (fun a => !p a)).numerator = d.total :=
  eventMass_complement _ _ _

theorem probability_mono (d : Distribution α) (p q : α → Bool)
    (h : ∀ a, a ∈ d.outcomes → p a = true → q a = true) :
    (d.probability p).numerator ≤ (d.probability q).numerator := eventMass_mono _ _ _ _ h

theorem probability_disjoint_union (d : Distribution α) (p q : α → Bool)
    (h : ∀ a, a ∈ d.outcomes → p a = true → q a = false) :
    (d.probability (fun a => p a || q a)).numerator =
      (d.probability p).numerator + (d.probability q).numerator := eventMass_disjoint_union _ _ _ _ h

/-- Uniform probability on positions of a nonempty list. Repeated values have
probability proportional to their number of occurrences. -/
def uniform (xs : List α) (nonempty : 0 < xs.length) : Distribution α where
  outcomes := xs
  weight := fun _ => 1
  positive := by simpa [mass_unit] using nonempty

@[simp] theorem uniform_total (xs : List α) (h : 0 < xs.length) : (uniform xs h).total = xs.length :=
  mass_unit xs

theorem uniform_probability_numerator (xs : List α) (h : 0 < xs.length) (p : α → Bool) :
    ((uniform xs h).probability p).numerator = (xs.filter p).length := by
  change eventMass (fun _ => 1) p xs = _
  rw [eventMass_filter, mass_unit]

/-- Zero-weight or empty outcome lists cannot define this normalized distribution. -/
theorem outcomes_nonempty (d : Distribution α) : d.outcomes ≠ [] := by
  intro h
  have hp := d.positive
  rw [h, mass_nil] at hp
  exact Nat.not_lt_zero _ hp

end Distribution
end JonnyLean.DiscreteProbability
