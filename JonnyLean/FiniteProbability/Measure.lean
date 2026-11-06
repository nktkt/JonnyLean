import JonnyLean.Counting.Dependent
namespace JonnyLean.FiniteProbability
open DiscreteProbability

/-- A finite list of weighted occurrences. Equal values need not be merged. -/
abbrev Measure (α : Type u) := List (α × Nat)

def total (μ : Measure α) : Nat := mass Prod.snd μ

def point (a : α) (n : Nat) : Measure α := [(a, n)]
def dirac (a : α) : Measure α := point a 1

@[simp] theorem total_nil : total ([] : Measure α) = 0 := rfl
@[simp] theorem total_cons (a : α) (n : Nat) (μ : Measure α) : total ((a, n) :: μ) = n + total μ := rfl

theorem total_append (μ ν : Measure α) : total (μ ++ ν) = total μ + total ν := mass_append _ _ _

theorem total_point (a : α) (n : Nat) : total (point a n) = n := Nat.add_zero n

theorem total_dirac (a : α) : total (dirac a) = 1 := rfl

theorem total_zero_weights (xs : List α) : total (xs.map (fun a => (a, 0))) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa using ih
end JonnyLean.FiniteProbability
