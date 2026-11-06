import JonnyLean.Languages.Concatenation
namespace JonnyLean.Languages

theorem concat_assoc (L K M : Language α) :
    concat (concat L K) M = concat L (concat K M) := by
  apply included_antisymm
  · rintro w ⟨uv, z, ⟨u, v, hu, hv, rfl⟩, hz, rfl⟩
    exact ⟨u, v ++ z, hu, ⟨v, z, hv, hz, rfl⟩, (List.append_assoc _ _ _).symm⟩
  · rintro w ⟨u, vz, hu, ⟨v, z, hv, hz, rfl⟩, rfl⟩
    exact ⟨u ++ v, z, ⟨u, v, hu, hv, rfl⟩, hz, List.append_assoc _ _ _⟩
theorem epsilon_concat (L : Language α) : concat epsilon L = L := by
  apply included_antisymm
  · rintro w ⟨u, v, rfl, hv, rfl⟩; exact hv
  · intro w hw; exact ⟨[], w, rfl, hw, rfl⟩
theorem concat_epsilon (L : Language α) : concat L epsilon = L := by
  apply included_antisymm
  · rintro w ⟨u, v, hu, rfl, rfl⟩; simpa using hu
  · intro w hw; exact ⟨w, [], hw, rfl, List.append_nil _⟩
theorem concat_singletons (u v : List α) :
    concat (fun w => w = u) (fun w => w = v) = (fun w => w = u ++ v) := by
  apply included_antisymm
  · rintro w ⟨a, b, rfl, rfl, h⟩; exact h.symm
  · intro w h; exact ⟨u, v, rfl, rfl, h.symm⟩
end JonnyLean.Languages
