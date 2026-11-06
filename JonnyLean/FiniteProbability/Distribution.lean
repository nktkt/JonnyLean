import JonnyLean.FiniteProbability.Events
import JonnyLean.DiscreteProbability.Distribution
namespace JonnyLean.FiniteProbability

structure Distribution (α : Type u) where
  measure : Measure α
  positive : 0 < total measure

namespace Distribution

def probability (d : Distribution α) (p : α → Bool) : DiscreteProbability.Probability where
  numerator := event d.measure p
  denominator := total d.measure
  positive := d.positive
  bounded := event_le d.measure p

def map (d : Distribution α) (f : α → β) : Distribution β where
  measure := push f d.measure
  positive := by rw [total_push]; exact d.positive

theorem probability_map (d : Distribution α) (f : α → β) (p : β → Bool) :
    ((d.map f).probability p).numerator = (d.probability (fun a => p (f a))).numerator :=
  event_push f d.measure p

theorem map_denominator (d : Distribution α) (f : α → β) (p : β → Bool) :
    ((d.map f).probability p).denominator = total d.measure := total_push f d.measure

theorem probability_complement (d : Distribution α) (p : α → Bool) :
    (d.probability p).numerator + (d.probability (fun a => !p a)).numerator =
      (d.probability p).denominator := event_complement d.measure p

theorem measure_nonempty (d : Distribution α) : d.measure ≠ [] := by
  intro h
  have hp := d.positive
  rw [h, total_nil] at hp
  exact Nat.not_lt_zero _ hp
end Distribution
end JonnyLean.FiniteProbability
