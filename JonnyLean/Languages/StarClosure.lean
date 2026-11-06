import JonnyLean.Languages.Star
namespace JonnyLean.Languages

theorem star_idempotent (L : Language α) : Star (Star L) = Star L := by
  apply included_antisymm
  · exact star_minimal Star.nil (included_refl _) (fun _ _ => star_append)
  · exact fun _ h => star_single h
theorem star_concat (L : Language α) : concat (Star L) (Star L) = Star L := by
  apply included_antisymm
  · rintro w ⟨u, v, hu, hv, rfl⟩; exact star_append hu hv
  · intro w hw; exact ⟨w, [], hw, .nil, List.append_nil _⟩
theorem star_empty : Star (empty : Language α) = epsilon := by
  apply included_antisymm
  · intro w hw
    induction hw with
    | nil => rfl
    | step hu hv ih => exact hu.elim
  · intro w hw; cases hw; exact .nil

theorem star_iff_power (L : Language α) (w : List α) : Star L w ↔ ∃ n, power L n w := by
  constructor
  · intro hw
    induction hw with
    | nil => exact ⟨0, rfl⟩
    | @step u v hu hv ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, u, v, hu, hn, rfl⟩
  · rintro ⟨n, hn⟩; exact power_in_star L n w hn
end JonnyLean.Languages
