import JonnyLean.FiniteProbability.Mixture
namespace JonnyLean.FiniteProbability

/-- A finite weighted transition kernel; no fixed row total is assumed. -/
def bind (μ : Measure α) (k : α → Measure β) : Measure β :=
  μ.flatMap (fun p => scale p.2 (k p.1))

theorem expect_bind (μ : Measure α) (k : α → Measure β) (f : β → Nat) :
    expect (bind μ k) f = expect μ (fun a => expect (k a) f) := by
  unfold bind expect
  rw [Counting.mass_flatMap]
  change DiscreteProbability.mass (fun p => expect (scale p.2 (k p.1)) f) μ = _
  simp only [expect_scale]
  rfl

theorem total_bind (μ : Measure α) (k : α → Measure β) :
    total (bind μ k) = expect μ (fun a => total (k a)) := by
  have h := expect_bind μ k (fun _ => 1)
  simpa [expect_const] using h

theorem total_bind_constant (μ : Measure α) (k : α → Measure β) (n : Nat)
    (h : ∀ a, total (k a) = n) : total (bind μ k) = total μ * n := by
  rw [total_bind]
  simp only [h]
  exact expect_const μ n

theorem bind_append (μ ν : Measure α) (k : α → Measure β) :
    bind (μ ++ ν) k = bind μ k ++ bind ν k := List.flatMap_append

theorem bind_dirac (a : α) (k : α → Measure β) : bind (dirac a) k = k a := by
  simp [bind, dirac, point, scale_one]
end JonnyLean.FiniteProbability
