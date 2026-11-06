import JonnyLean.Languages.Power
namespace JonnyLean.Languages

inductive Star (L : Language α) : List α → Prop where
  | nil : Star L []
  | step {u v : List α} : L u → Star L v → Star L (u ++ v)

theorem star_single {L : Language α} {w : List α} (h : L w) : Star L w := by
  simpa using Star.step h Star.nil

theorem star_append {L : Language α} {u v : List α} (hu : Star L u) (hv : Star L v) :
    Star L (u ++ v) := by
  induction hu with
  | nil => exact hv
  | @step x y hx hy ih => simpa [List.append_assoc] using Star.step hx ih

theorem star_mono {L K : Language α} (h : Included L K) : Included (Star L) (Star K) := by
  intro w hw
  induction hw with
  | nil => exact .nil
  | @step u v hu hv ih => exact .step (h u hu) ih

theorem star_minimal {L K : Language α} (hnil : K []) (hbase : Included L K)
    (happend : ∀ u v, K u → K v → K (u ++ v)) : Included (Star L) K := by
  intro w hw
  induction hw with
  | nil => exact hnil
  | @step u v hu hv ih => exact happend u v (hbase u hu) ih

theorem power_in_star (L : Language α) (n : Nat) : Included (power L n) (Star L) := by
  induction n with
  | zero => intro w h; cases h; exact .nil
  | succ n ih =>
    rintro w ⟨u, v, hu, hv, rfl⟩
    exact .step hu (ih v hv)
end JonnyLean.Languages
