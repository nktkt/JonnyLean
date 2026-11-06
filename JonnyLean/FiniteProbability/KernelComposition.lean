import JonnyLean.FiniteProbability.Kernel
namespace JonnyLean.FiniteProbability

theorem bind_scale (n : Nat) (μ : Measure α) (k : α → Measure β) :
    bind (scale n μ) k = scale n (bind μ k) := by
  induction μ with
  | nil => rfl
  | cons p μ ih =>
    cases p with
    | mk a m =>
      change scale (n * m) (k a) ++ bind (scale n μ) k = scale n (scale m (k a) ++ bind μ k)
      rw [scale_append, scale_scale, ih]

theorem bind_assoc (μ : Measure α) (k : α → Measure β) (l : β → Measure γ) :
    bind (bind μ k) l = bind μ (fun a => bind (k a) l) := by
  induction μ with
  | nil => rfl
  | cons p μ ih =>
    cases p with
    | mk a n =>
      change bind (scale n (k a) ++ bind μ k) l = _
      rw [bind_append, bind_scale, ih]
      rfl

theorem bind_right_dirac (μ : Measure α) : bind μ dirac = μ := by
  induction μ with
  | nil => rfl
  | cons p μ ih => cases p; simp [bind, scale, dirac, point] at ih ⊢

theorem bind_point_map (μ : Measure α) (f : α → β) :
    bind μ (fun a => dirac (f a)) = push f μ := by
  induction μ with
  | nil => rfl
  | cons p μ ih => cases p; simp [bind, scale, dirac, point, push] at ih ⊢; exact ih
end JonnyLean.FiniteProbability
