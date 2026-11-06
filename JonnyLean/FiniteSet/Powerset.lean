import JonnyLean.FiniteSet.Basic

namespace JonnyLean.FiniteSet

/-- Enumerate every subsequence, preserving the source order. -/
def subsequences : List α → List (List α)
  | [] => [[]]
  | a :: xs => subsequences xs ++ (subsequences xs).map (List.cons a)

/-- Membership in the enumeration is exactly the sublist relation. -/
theorem mem_subsequences (xs ys : List α) : ys ∈ subsequences xs ↔ ys.Sublist xs := by
  induction xs generalizing ys with
  | nil => simp [subsequences]
  | cons a xs ih =>
    simp only [subsequences, List.mem_append, List.mem_map, List.sublist_cons_iff, ih]
    constructor
    · intro h
      cases h with
      | inl h => exact Or.inl h
      | inr h =>
        obtain ⟨ys, hy, he⟩ := h
        exact Or.inr ⟨ys, he.symm, hy⟩
    · intro h
      cases h with
      | inl h => exact Or.inl h
      | inr h =>
        obtain ⟨ys, he, hy⟩ := h
        exact Or.inr ⟨ys, hy, he.symm⟩

/-- A duplicate-free source produces no repeated subsequences. -/
theorem nodup_subsequences (xs : List α) (hn : xs.Nodup) : (subsequences xs).Nodup := by
  induction xs with
  | nil => simp [subsequences]
  | cons a xs ih =>
    have ha := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    apply List.nodup_append.mpr
    refine ⟨ih ht, ?_, ?_⟩
    · exact List.Pairwise.map _ (fun _ _ h he => h (List.cons.inj he).2) (ih ht)
    · intro s hs t ht he
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
      have hin : a ∈ s := he ▸ List.mem_cons_self
      exact ha (((mem_subsequences xs s).mp hs).subset hin)

/-- Count the enumeration by splitting subsets according to the first member. -/
theorem length_subsequences (xs : List α) : (subsequences xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [subsequences, List.length_append, List.length_map, ih, List.length_cons,
      Nat.pow_succ, Nat.mul_two]

/-- Build the powerset as finite sets with proofs of duplicate-free membership.
Each member uses the unique subsequence of the original enumeration. -/
def powerset (A : FiniteSet α) : FiniteSet (FiniteSet α) where
  elems := (subsequences A.elems).pmap
    (fun xs hn => (⟨xs, hn⟩ : FiniteSet α))
    (fun xs hx => ((mem_subsequences A.elems xs).mp hx).nodup A.nodup)
  nodup := by
    apply List.Pairwise.pmap (nodup_subsequences A.elems A.nodup)
    intro x hx y hy h he
    exact h (congrArg FiniteSet.elems he)

/-- The cardinality of the powerset of any finite set is two to its cardinality. -/
theorem card_powerset (A : FiniteSet α) : card (powerset A) = 2 ^ card A := by
  change (List.pmap _ _ _).length = 2 ^ A.elems.length
  rw [List.length_pmap, length_subsequences]

/-- Precisely the canonical, order-preserving representatives occur. -/
theorem mem_powerset (A B : FiniteSet α) : B ∈ powerset A ↔ B.elems.Sublist A.elems := by
  change B ∈ List.pmap _ _ _ ↔ _
  rw [List.mem_pmap]
  constructor
  · intro h
    obtain ⟨xs, hx, he⟩ := h
    have hv := congrArg FiniteSet.elems he
    exact hv ▸ (mem_subsequences A.elems xs).mp hx
  · intro h
    exact ⟨B.elems, (mem_subsequences A.elems B.elems).mpr h, rfl⟩

/-- Every enumerated set is a subset in the usual membership sense. -/
theorem powerset_sound (A B : FiniteSet α) (h : B ∈ powerset A) : Subset B A :=
  fun _ hx => ((mem_powerset A B).mp h).subset hx

/-- Every finite subset is represented, regardless of its own enumeration order. -/
theorem powerset_complete [DecidableEq α] (A B : FiniteSet α) (h : Subset B A) :
    ∃ C, C ∈ powerset A ∧ Equivalent B C := by
  let C : FiniteSet α := ⟨A.elems.filter (fun x => decide (x ∈ B.elems)),
    List.Pairwise.filter _ A.nodup⟩
  refine ⟨C, (mem_powerset A C).mpr List.filter_sublist, ?_⟩
  intro x
  change x ∈ B.elems ↔ x ∈ A.elems.filter _
  rw [List.mem_filter]
  constructor
  · intro hx
    exact ⟨h x hx, decide_eq_true hx⟩
  · intro hx
    exact of_decide_eq_true hx.2

/-- Within one duplicate-free enumeration, membership determines a sublist
uniquely. Thus reordered lists cannot be counted as different subsets. -/
theorem sublist_eq_of_members (xs : List α) (hn : xs.Nodup)
    (ys zs : List α) (hy : ys.Sublist xs) (hz : zs.Sublist xs)
    (he : ∀ x, x ∈ ys ↔ x ∈ zs) : ys = zs := by
  induction xs generalizing ys zs with
  | nil =>
    exact (List.eq_nil_of_sublist_nil hy).trans (List.eq_nil_of_sublist_nil hz).symm
  | cons a xs ih =>
    have ha := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    cases List.sublist_cons_iff.mp hy with
    | inl hy =>
      cases List.sublist_cons_iff.mp hz with
      | inl hz => exact ih ht ys zs hy hz he
      | inr hz =>
        obtain ⟨zs, rfl, hzt⟩ := hz
        exact False.elim (ha (hy.subset ((he a).mpr List.mem_cons_self)))
    | inr hy =>
      obtain ⟨ys, rfl, hyt⟩ := hy
      cases List.sublist_cons_iff.mp hz with
      | inl hz =>
        exact False.elim (ha (hz.subset ((he a).mp List.mem_cons_self)))
      | inr hz =>
        obtain ⟨zs, rfl, hzt⟩ := hz
        apply congrArg (List.cons a)
        apply ih ht ys zs hyt hzt
        intro x
        constructor
        · intro hx
          cases List.mem_cons.mp ((he x).mp (List.mem_cons_of_mem a hx)) with
          | inl hxa => exact False.elim (ha (hxa ▸ hyt.subset hx))
          | inr hxz => exact hxz
        · intro hx
          cases List.mem_cons.mp ((he x).mpr (List.mem_cons_of_mem a hx)) with
          | inl hxa => exact False.elim (ha (hxa ▸ hzt.subset hx))
          | inr hxy => exact hxy

/-- There is only one representative of each mathematical subset in the powerset. -/
theorem powerset_unique (A B C : FiniteSet α)
    (hb : B ∈ powerset A) (hc : C ∈ powerset A) (he : Equivalent B C) : B = C := by
  have hv := sublist_eq_of_members A.elems A.nodup B.elems C.elems
    ((mem_powerset A B).mp hb) ((mem_powerset A C).mp hc) he
  cases B
  cases C
  cases hv
  rfl

end JonnyLean.FiniteSet

