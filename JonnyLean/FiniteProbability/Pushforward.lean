import JonnyLean.FiniteProbability.Measure
namespace JonnyLean.FiniteProbability

def push (f : α → β) (μ : Measure α) : Measure β := μ.map (fun p => (f p.1, p.2))

theorem total_push (f : α → β) (μ : Measure α) : total (push f μ) = total μ :=
  Counting.mass_map _ _ _

theorem push_id (μ : Measure α) : push id μ = μ := by
  induction μ with
  | nil => rfl
  | cons a μ ih => cases a; simp [push] at ih ⊢

theorem push_comp (f : α → β) (g : β → γ) (μ : Measure α) :
    push g (push f μ) = push (fun a => g (f a)) μ := by simp [push, List.map_map]

theorem push_append (f : α → β) (μ ν : Measure α) : push f (μ ++ ν) = push f μ ++ push f ν := List.map_append

theorem push_dirac (f : α → β) (a : α) : push f (dirac a) = dirac (f a) := rfl
end JonnyLean.FiniteProbability
