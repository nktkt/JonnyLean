import JonnyLean.FiniteProbability.Pushforward
import JonnyLean.Counting.WeightedSubsequences
namespace JonnyLean.FiniteProbability
open DiscreteProbability

/-- Unnormalized numerator of the expectation of a natural-valued observable. -/
def expect (μ : Measure α) (f : α → Nat) : Nat := mass (fun p => p.2 * f p.1) μ

@[simp] theorem expect_nil (f : α → Nat) : expect [] f = 0 := rfl
@[simp] theorem expect_cons (a : α) (n : Nat) (μ : Measure α) (f : α → Nat) :
    expect ((a, n) :: μ) f = n * f a + expect μ f := rfl

theorem expect_add (μ : Measure α) (f g : α → Nat) :
    expect μ (fun a => f a + g a) = expect μ f + expect μ g := by
  unfold expect
  simp only [Nat.mul_add]
  exact Counting.mass_add_weights _ _ _

theorem expect_scalar (μ : Measure α) (c : Nat) (f : α → Nat) :
    expect μ (fun a => c * f a) = c * expect μ f := by
  induction μ with
  | nil => simp
  | cons p μ ih => cases p; simp [ih, Nat.mul_add, Nat.mul_left_comm]

theorem expect_const (μ : Measure α) (c : Nat) : expect μ (fun _ => c) = total μ * c := by
  induction μ with
  | nil => simp
  | cons p μ ih => cases p; simp [ih, Nat.add_mul]

theorem expect_append (μ ν : Measure α) (f : α → Nat) :
    expect (μ ++ ν) f = expect μ f + expect ν f := mass_append _ _ _

theorem expect_push (f : α → β) (μ : Measure α) (g : β → Nat) :
    expect (push f μ) g = expect μ (fun a => g (f a)) := Counting.mass_map _ _ _

theorem expect_mono (μ : Measure α) (f g : α → Nat) (h : ∀ a, f a ≤ g a) : expect μ f ≤ expect μ g := by
  induction μ with
  | nil => exact Nat.le_refl _
  | cons p μ ih => exact Nat.add_le_add (Nat.mul_le_mul_left p.2 (h p.1)) ih
end JonnyLean.FiniteProbability
