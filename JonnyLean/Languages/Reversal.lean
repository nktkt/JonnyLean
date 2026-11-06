import JonnyLean.Languages.Monoid
namespace JonnyLean.Languages

def reverse (L : Language α) : Language α := fun w => L w.reverse

theorem reverse_reverse (L : Language α) : reverse (reverse L) = L := by
  funext w; simp [reverse]
theorem reverse_union (L K : Language α) : reverse (union L K) = union (reverse L) (reverse K) := rfl
theorem reverse_epsilon : reverse (epsilon : Language α) = epsilon := by
  funext w; simp [reverse, epsilon]
theorem reverse_concat (L K : Language α) :
    reverse (concat L K) = concat (reverse K) (reverse L) := by
  apply included_antisymm
  · rintro w ⟨u, v, hu, hv, h⟩
    refine ⟨v.reverse, u.reverse, ?_, ?_, ?_⟩
    · simpa [reverse] using hv
    · simpa [reverse] using hu
    · have := congrArg List.reverse h
      simpa using this
  · rintro w ⟨u, v, hu, hv, rfl⟩
    exact ⟨v.reverse, u.reverse, hv, hu, List.reverse_append.symm⟩
end JonnyLean.Languages
