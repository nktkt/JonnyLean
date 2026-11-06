import JonnyLean.FiniteProbability.Events
namespace JonnyLean.FiniteProbability

def restrict (μ : Measure α) (p : α → Bool) : Measure α := μ.filter (fun z => p z.1)

theorem expect_restrict (μ : Measure α) (p : α → Bool) (f : α → Nat) :
    expect (restrict μ p) f = expect μ (fun a => if p a then f a else 0) := by
  induction μ with
  | nil => rfl
  | cons z μ ih =>
    cases z with
    | mk a n => cases hp : p a <;> simpa [restrict, List.filter, hp] using ih

theorem total_restrict (μ : Measure α) (p : α → Bool) : total (restrict μ p) = event μ p := by
  have h := expect_restrict μ p (fun _ => 1)
  simpa [expect_const, event, indicator] using h

theorem restrict_restrict (μ : Measure α) (p q : α → Bool) :
    restrict (restrict μ p) q = restrict μ (fun a => p a && q a) := by
  simp [restrict, List.filter_filter, Bool.and_comm]

theorem restrict_comm (μ : Measure α) (p q : α → Bool) :
    restrict (restrict μ p) q = restrict (restrict μ q) p := by
  simp [restrict_restrict, Bool.and_comm]

theorem event_restrict (μ : Measure α) (p q : α → Bool) :
    event (restrict μ p) q = event μ (fun a => p a && q a) := by
  rw [← total_restrict, restrict_restrict, total_restrict]
end JonnyLean.FiniteProbability
