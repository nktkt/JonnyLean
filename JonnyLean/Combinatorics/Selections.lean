import Init.Data.List.Sublist

namespace JonnyLean.Combinatorics

/-- Enumerate selections of k positions in order. Equal source values are still
different positions and may yield repeated output lists. -/
def selections : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, a :: xs => (selections k xs).map (fun ys => a :: ys) ++ selections (k + 1) xs

@[simp] theorem selections_zero (xs : List α) : selections 0 xs = [[]] := by cases xs <;> rfl
@[simp] theorem selections_nil_succ (k : Nat) : selections (k + 1) ([] : List α) = [] := rfl
@[simp] theorem selections_cons_succ (k : Nat) (a : α) (xs : List α) :
    selections (k + 1) (a :: xs) =
      (selections k xs).map (fun ys => a :: ys) ++ selections (k + 1) xs := rfl

theorem mem_selections_length {xs ys : List α} {k : Nat}
    (h : ys ∈ selections k xs) : ys.length = k := by
  induction xs generalizing k ys with
  | nil =>
    cases k with
    | zero => have : ys = [] := by simpa [selections] using h
              subst ys
              rfl
    | succ k => simp [selections] at h
  | cons a xs ih =>
    cases k with
    | zero => have : ys = [] := by simpa [selections] using h
              subst ys
              rfl
    | succ k =>
      cases List.mem_append.mp h with
      | inl h =>
        obtain ⟨zs, hz, rfl⟩ := List.mem_map.mp h
        simp [ih hz]
      | inr h => exact ih h

/-- No output contains a value absent from the source list. -/
theorem mem_of_mem_selection {xs ys : List α} {k : Nat}
    (h : ys ∈ selections k xs) {a : α} (ha : a ∈ ys) : a ∈ xs := by
  induction xs generalizing k ys with
  | nil =>
    cases k with
    | zero => have : ys = [] := by simpa [selections] using h
              subst ys
              exact False.elim (List.not_mem_nil ha)
    | succ k => simp [selections] at h
  | cons b xs ih =>
    cases k with
    | zero => have : ys = [] := by simpa [selections] using h
              subst ys
              exact False.elim (List.not_mem_nil ha)
    | succ k =>
      cases List.mem_append.mp h with
      | inl h =>
        obtain ⟨zs, hz, rfl⟩ := List.mem_map.mp h
        cases List.mem_cons.mp ha with
        | inl he => exact List.mem_cons.mpr (.inl he)
        | inr ht => exact List.mem_cons_of_mem b (ih hz ht)
      | inr h => exact List.mem_cons_of_mem b (ih h ha)


theorem selections_too_many (xs : List α) (k : Nat) (h : xs.length < k) : selections k xs = [] := by
  induction xs generalizing k with
  | nil => cases k with
           | zero => exact False.elim (Nat.not_lt_zero _ h)
           | succ k => rfl
  | cons a xs ih =>
    cases k with
    | zero => exact False.elim (Nat.not_lt_zero _ h)
    | succ k =>
      have hx : xs.length < k := Nat.lt_of_succ_lt_succ h
      rw [selections_cons_succ, ih k hx, ih (k + 1) (Nat.lt_trans hx (Nat.lt_succ_self k))]
      rfl

/-- Selecting every position has exactly one result. -/
theorem selections_full (xs : List α) : selections xs.length xs = [xs] := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.length_cons, selections_cons_succ, ih, selections_too_many xs (xs.length + 1) (Nat.lt_succ_self _)]
    rfl

/-- Each selection is a subsequence, so the original order is preserved. -/
theorem sublist_of_mem_selections {xs ys : List α} {k : Nat}
    (h : ys ∈ selections k xs) : ys.Sublist xs := by
  induction xs generalizing k ys with
  | nil =>
    cases k with
    | zero => have : ys = [] := by simpa [selections] using h
              subst ys
              exact .slnil
    | succ k => simp [selections] at h
  | cons a xs ih =>
    cases k with
    | zero => have : ys = [] := by simpa [selections] using h
              subst ys
              exact List.nil_sublist _
    | succ k =>
      cases List.mem_append.mp h with
      | inl h =>
        obtain ⟨zs, hz, rfl⟩ := List.mem_map.mp h
        exact (ih hz).cons₂ a
      | inr h => exact (ih h).cons a

/-- Every subsequence occurs when its length is requested. -/
theorem mem_selections_of_sublist {xs ys : List α} (h : ys.Sublist xs) :
    ys ∈ selections ys.length xs := by
  induction h with
  | slnil => exact List.mem_cons_self
  | @cons ys xs a h ih =>
    cases ys with
    | nil => simp
    | cons b ys => exact List.mem_append.mpr (.inr ih)
  | @cons₂ ys xs a h ih =>
    exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨ys, ih, rfl⟩))

/-- Exact membership semantics: ordered subsequence and requested length. -/
theorem mem_selections_iff {xs ys : List α} {k : Nat} :
    ys ∈ selections k xs ↔ ys.Sublist xs ∧ ys.length = k := by
  constructor
  · intro h
    exact ⟨sublist_of_mem_selections h, mem_selections_length h⟩
  · intro h
    rw [← h.2]
    exact mem_selections_of_sublist h.1

end JonnyLean.Combinatorics
