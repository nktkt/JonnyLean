import Init.Data.List.Lemmas

namespace JonnyLean.Combinatorics

/-- Enumerate length-n words over the listed alphabet. Repeated alphabet entries
produce repeated words, so this is an enumeration with multiplicity. -/
def words (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap (fun a => (words alphabet n).map (fun w => a :: w))

@[simp] theorem words_zero (alphabet : List α) : words alphabet 0 = [[]] := rfl
@[simp] theorem words_succ (alphabet : List α) (n : Nat) :
    words alphabet (n + 1) = alphabet.flatMap (fun a => (words alphabet n).map (fun w => a :: w)) := rfl

/-- Membership has exactly the intended length and letter semantics. -/
theorem mem_words (alphabet : List α) (n : Nat) (w : List α) :
    w ∈ words alphabet n ↔ w.length = n ∧ ∀ a, a ∈ w → a ∈ alphabet := by
  induction n generalizing w with
  | zero =>
    constructor
    · intro h
      have hw : w = [] := by simpa [words] using h
      subst w
      simp
    · intro h
      have hw : w = [] := List.length_eq_zero_iff.mp h.1
      subst w
      simp [words]
  | succ n ih =>
    constructor
    · intro h
      obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp h
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
      obtain ⟨hlen, hall⟩ := (ih t).mp ht
      constructor
      · simp [hlen]
      · intro b hb
        cases List.mem_cons.mp hb with
        | inl he => exact he ▸ ha
        | inr hb => exact hall b hb
    · intro h
      cases w with
      | nil => exact False.elim (Nat.noConfusion h.1)
      | cons a t =>
        apply List.mem_flatMap.mpr
        refine ⟨a, h.2 a List.mem_cons_self, ?_⟩
        apply List.mem_map.mpr
        refine ⟨t, (ih t).mpr ⟨?_, ?_⟩, rfl⟩
        · exact Nat.succ.inj h.1
        · intro b hb
          exact h.2 b (List.mem_cons_of_mem a hb)

theorem length_of_mem_words (h : w ∈ words alphabet n) : w.length = n := (mem_words alphabet n w).mp h |>.1

theorem letters_of_mem_words (h : w ∈ words alphabet n) (ha : a ∈ w) : a ∈ alphabet :=
  (mem_words alphabet n w).mp h |>.2 a ha

theorem words_mono (h : ∀ a, a ∈ alphabet → a ∈ larger) (hw : w ∈ words alphabet n) :
    w ∈ words larger n := by
  obtain ⟨hl, ha⟩ := (mem_words alphabet n w).mp hw
  exact (mem_words larger n w).mpr ⟨hl, fun a hmem => h a (ha a hmem)⟩

end JonnyLean.Combinatorics
