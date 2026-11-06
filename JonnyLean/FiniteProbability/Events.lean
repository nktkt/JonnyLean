import JonnyLean.FiniteProbability.Product
namespace JonnyLean.FiniteProbability

def indicator (p : α → Bool) (a : α) : Nat := if p a then 1 else 0
def event (μ : Measure α) (p : α → Bool) : Nat := expect μ (indicator p)

theorem event_complement (μ : Measure α) (p : α → Bool) :
    event μ p + event μ (fun a => !p a) = total μ := by
  unfold event
  rw [← expect_add]
  have h : (fun a => indicator p a + indicator (fun a => !p a) a) = (fun _ => 1) := by
    funext a
    change (if p a then 1 else 0) + (if Bool.not (p a) then 1 else 0) = 1
    cases p a <;> rfl
  rw [h, expect_const, Nat.mul_one]

theorem event_le (μ : Measure α) (p : α → Bool) : event μ p ≤ total μ := by
  have h := event_complement μ p
  omega

theorem event_product (μ : Measure α) (ν : Measure β) (p : α → Bool) (q : β → Bool) :
    event (product μ ν) (fun z => p z.1 && q z.2) = event μ p * event ν q := by
  unfold event
  have h : indicator (fun z : α × β => p z.1 && q z.2) =
      (fun z => indicator p z.1 * indicator q z.2) := by
    funext z
    change (if p z.1 && q z.2 then 1 else 0) =
      (if p z.1 then 1 else 0) * (if q z.2 then 1 else 0)
    cases p z.1 <;> cases q z.2 <;> rfl
  rw [h, expect_product]

theorem event_push (f : α → β) (μ : Measure α) (p : β → Bool) :
    event (push f μ) p = event μ (fun a => p (f a)) := expect_push f μ _

theorem event_false (μ : Measure α) : event μ (fun _ => false) = 0 := by
  change expect μ (fun _ => 0) = 0
  rw [expect_const, Nat.mul_zero]
end JonnyLean.FiniteProbability
