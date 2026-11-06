import JonnyLean.Languages.Lattice
namespace JonnyLean.Languages

def concat (L K : Language α) : Language α :=
  fun w => ∃ u v, L u ∧ K v ∧ u ++ v = w

theorem concat_intro {L K : Language α} {u v : List α} (hu : L u) (hv : K v) :
    concat L K (u ++ v) := ⟨u, v, hu, hv, rfl⟩
theorem concat_mono {L K M N : Language α} (h : Included L M) (g : Included K N) :
    Included (concat L K) (concat M N) := by
  rintro w ⟨u, v, hu, hv, rfl⟩
  exact ⟨u, v, h u hu, g v hv, rfl⟩
theorem concat_empty (L : Language α) : concat L empty = empty := by
  apply included_antisymm
  · rintro w ⟨u, v, hu, hv, he⟩; exact hv
  · exact empty_included _
theorem empty_concat (L : Language α) : concat empty L = empty := by
  apply included_antisymm
  · rintro w ⟨u, v, hu, hv, he⟩; exact hu
  · exact empty_included _
theorem concat_union (L K M : Language α) :
    concat L (union K M) = union (concat L K) (concat L M) := by
  apply included_antisymm
  · rintro w ⟨u, v, hu, hv | hv, rfl⟩
    · exact .inl ⟨u, v, hu, hv, rfl⟩
    · exact .inr ⟨u, v, hu, hv, rfl⟩
  · rintro w (⟨u, v, hu, hv, rfl⟩ | ⟨u, v, hu, hv, rfl⟩)
    · exact ⟨u, v, hu, .inl hv, rfl⟩
    · exact ⟨u, v, hu, .inr hv, rfl⟩
end JonnyLean.Languages
