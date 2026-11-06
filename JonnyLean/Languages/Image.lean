import JonnyLean.Languages.StarClosure
import JonnyLean.Languages.Reversal
namespace JonnyLean.Languages

def image (f : α → β) (L : Language α) : Language β := fun w => ∃ u, L u ∧ u.map f = w

theorem image_id (L : Language α) : image id L = L := by
  apply included_antisymm
  · rintro w ⟨u, hu, rfl⟩; simpa using hu
  · intro w hw; exact ⟨w, hw, List.map_id w⟩
theorem image_comp (f : α → β) (g : β → γ) (L : Language α) :
    image g (image f L) = image (fun a => g (f a)) L := by
  apply included_antisymm
  · rintro w ⟨v, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, (List.map_map).symm⟩
  · rintro w ⟨u, hu, rfl⟩; exact ⟨u.map f, ⟨u, hu, rfl⟩, List.map_map⟩
theorem image_concat (f : α → β) (L K : Language α) :
    image f (concat L K) = concat (image f L) (image f K) := by
  apply included_antisymm
  · rintro w ⟨uv, ⟨u, v, hu, hv, rfl⟩, rfl⟩
    exact ⟨u.map f, v.map f, ⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, (List.map_append).symm⟩
  · rintro w ⟨u, v, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x ++ y, ⟨x, y, hx, hy, rfl⟩, List.map_append⟩
theorem image_star (f : α → β) (L : Language α) : image f (Star L) = Star (image f L) := by
  apply included_antisymm
  · rintro w ⟨u, hu, rfl⟩
    induction hu with
    | nil => exact .nil
    | @step x y hx hy ih => simpa using Star.step (⟨x, hx, rfl⟩ : image f L (x.map f)) ih
  · intro w hw
    induction hw with
    | nil => exact ⟨[], .nil, rfl⟩
    | @step x y hx hy ih =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := ih
      exact ⟨u ++ v, .step hu hv, List.map_append⟩
end JonnyLean.Languages
