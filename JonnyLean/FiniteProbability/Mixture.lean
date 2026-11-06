import JonnyLean.FiniteProbability.Expectation
namespace JonnyLean.FiniteProbability

def scale (n : Nat) (μ : Measure α) : Measure α := μ.map (fun p => (p.1, n * p.2))

def mix (m : Nat) (μ : Measure α) (n : Nat) (ν : Measure α) : Measure α := scale m μ ++ scale n ν

theorem expect_scale (n : Nat) (μ : Measure α) (f : α → Nat) :
    expect (scale n μ) f = n * expect μ f := by
  unfold expect scale
  rw [Counting.mass_map]
  simp only [Nat.mul_assoc]
  exact Counting.mass_scale_left _ _ _

theorem total_scale (n : Nat) (μ : Measure α) : total (scale n μ) = n * total μ := by
  have h := expect_scale n μ (fun _ => 1)
  simpa [expect_const] using h

theorem expect_mix (m : Nat) (μ : Measure α) (n : Nat) (ν : Measure α) (f : α → Nat) :
    expect (mix m μ n ν) f = m * expect μ f + n * expect ν f := by
  rw [mix, expect_append, expect_scale, expect_scale]

theorem total_mix (m : Nat) (μ : Measure α) (n : Nat) (ν : Measure α) :
    total (mix m μ n ν) = m * total μ + n * total ν := by
  rw [mix, total_append, total_scale, total_scale]

theorem scale_append (n : Nat) (μ ν : Measure α) : scale n (μ ++ ν) = scale n μ ++ scale n ν := List.map_append

theorem scale_scale (m n : Nat) (μ : Measure α) : scale m (scale n μ) = scale (m * n) μ := by
  simp [scale, List.map_map, Nat.mul_assoc]

theorem scale_one (μ : Measure α) : scale 1 μ = μ := by
  induction μ with
  | nil => rfl
  | cons z μ ih => cases z; simp [scale] at ih ⊢
end JonnyLean.FiniteProbability
