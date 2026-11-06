import Std

namespace JonnyLean.Algorithms

/-- Split immediately before the first accepted element, or at the end if none exists. -/
def firstMatchSplit (p : α → Bool) : List α → List α × List α
  | [] => ([], [])
  | x :: xs => if p x then ([], x :: xs) else
      let rest := firstMatchSplit p xs
      (x :: rest.1, rest.2)

theorem firstMatchSplit_reassembles (p : α → Bool) (xs : List α) :
    (firstMatchSplit p xs).1 ++ (firstMatchSplit p xs).2 = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [firstMatchSplit, h, ih]

theorem firstMatchSplit_prefix_rejects (p : α → Bool) (xs : List α) :
    ∀ x ∈ (firstMatchSplit p xs).1, p x = false := by
  induction xs with
  | nil => simp [firstMatchSplit]
  | cons a xs ih =>
    cases h : p a
    · simp only [firstMatchSplit, h, Bool.false_eq_true, ↓reduceIte]
      intro x hx
      cases List.mem_cons.mp hx with
      | inl hxa => exact hxa ▸ h
      | inr hx => exact ih x hx
    · simp [firstMatchSplit, h]

theorem firstMatchSplit_head_accepts (p : α → Bool) (xs : List α) (x : α) (tail : List α)
    (h : (firstMatchSplit p xs).2 = x :: tail) : p x = true := by
  induction xs with
  | nil => simp [firstMatchSplit] at h
  | cons a xs ih =>
    cases ha : p a
    · exact ih (by simpa only [firstMatchSplit, ha, Bool.false_eq_true, ↓reduceIte] using h)
    · have he : a = x := (List.cons.inj (by simpa [firstMatchSplit, ha] using h)).1
      exact he ▸ ha

theorem firstMatchSplit_empty_iff (p : α → Bool) (xs : List α) :
    (firstMatchSplit p xs).2 = [] ↔ ∀ x ∈ xs, p x = false := by
  constructor
  · intro h
    have he := firstMatchSplit_reassembles p xs
    rw [h, List.append_nil] at he
    rw [← he]
    exact firstMatchSplit_prefix_rejects p xs
  · intro h
    cases hs : (firstMatchSplit p xs).2 with
    | nil => rfl
    | cons x tail =>
      have hx : x ∈ xs := by
        rw [← firstMatchSplit_reassembles p xs, hs]
        exact List.mem_append.mpr (Or.inr List.mem_cons_self)
      have ht := firstMatchSplit_head_accepts p xs x tail hs
      exact False.elim (Bool.noConfusion (ht.symm.trans (h x hx)))

theorem firstMatchSplit_certificate (p : α → Bool) (xs : List α) :
    xs = (firstMatchSplit p xs).1 ++ (firstMatchSplit p xs).2 ∧
    (∀ x ∈ (firstMatchSplit p xs).1, p x = false) ∧
    (∀ x tail, (firstMatchSplit p xs).2 = x :: tail → p x = true) :=
  ⟨(firstMatchSplit_reassembles p xs).symm, firstMatchSplit_prefix_rejects p xs,
    firstMatchSplit_head_accepts p xs⟩

end JonnyLean.Algorithms
