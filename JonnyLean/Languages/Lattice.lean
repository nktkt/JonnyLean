import JonnyLean.Languages.Basic
namespace JonnyLean.Languages

theorem union_comm (L K : Language α) : union L K = union K L := by
  funext w; exact propext Or.comm
theorem union_assoc (L K M : Language α) : union (union L K) M = union L (union K M) := by
  funext w; exact propext or_assoc
theorem inter_comm (L K : Language α) : inter L K = inter K L := by
  funext w; exact propext And.comm
theorem inter_union (L K M : Language α) :
    inter L (union K M) = union (inter L K) (inter L M) := by
  funext w
  apply propext
  constructor
  · rintro ⟨hl, hk | hm⟩
    · exact .inl ⟨hl, hk⟩
    · exact .inr ⟨hl, hm⟩
  · rintro (⟨hl, hk⟩ | ⟨hl, hm⟩)
    · exact ⟨hl, .inl hk⟩
    · exact ⟨hl, .inr hm⟩
theorem union_empty (L : Language α) : union L empty = L := by
  funext w; exact propext ⟨fun h => h.elim id False.elim, Or.inl⟩
/-- All letters of a word satisfy the specified alphabet predicate. -/
def alphabetLanguage (A : α → Prop) : Language α := fun w => ∀ a, a ∈ w → A a

theorem alphabetLanguage_append (A : α → Prop) (u v : List α) :
    alphabetLanguage A (u ++ v) ↔ alphabetLanguage A u ∧ alphabetLanguage A v := by
  constructor
  · intro h
    exact ⟨fun a ha => h a (List.mem_append.mpr (.inl ha)),
      fun a ha => h a (List.mem_append.mpr (.inr ha))⟩
  · rintro ⟨hu, hv⟩ a ha
    exact (List.mem_append.mp ha).elim (hu a) (hv a)

theorem alphabetLanguage_inter (A B : α → Prop) :
    alphabetLanguage (fun a => A a ∧ B a) = inter (alphabetLanguage A) (alphabetLanguage B) := by
  apply included_antisymm
  · intro w hw
    exact ⟨fun a ha => (hw a ha).1, fun a ha => (hw a ha).2⟩
  · rintro w ⟨ha, hb⟩ a h
    exact ⟨ha a h, hb a h⟩

theorem alphabetLanguage_union_included (A B : α → Prop) :
    Included (union (alphabetLanguage A) (alphabetLanguage B)) (alphabetLanguage (fun a => A a ∨ B a)) := by
  intro w h a ha
  exact h.elim (fun h => .inl (h a ha)) (fun h => .inr (h a ha))

theorem alphabetLanguage_mono {A B : α → Prop} (h : ∀ a, A a → B a) :
    Included (alphabetLanguage A) (alphabetLanguage B) := fun _ hw a ha => h a (hw a ha)

theorem alphabetLanguage_nil (A : α → Prop) : alphabetLanguage A [] := by
  intro a ha
  exact False.elim (List.not_mem_nil ha)

end JonnyLean.Languages
