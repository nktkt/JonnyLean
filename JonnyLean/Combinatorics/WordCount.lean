import JonnyLean.Combinatorics.Words

namespace JonnyLean.Combinatorics

/-- Every branch of a list-indexed construction contributes the same number of items. -/
theorem length_flatMap_constant (xs : List α) (f : α → List β) (k : Nat)
    (h : ∀ a, a ∈ xs → (f a).length = k) :
    (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem a hb))]
    simp [Nat.succ_mul, Nat.add_comm]

/-- The multiplication principle gives the size of the word enumeration. -/
theorem length_words (alphabet : List α) (n : Nat) :
    (words alphabet n).length = alphabet.length ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [words_succ, length_flatMap_constant alphabet _ (alphabet.length ^ n)]
    · rw [Nat.pow_succ, Nat.mul_comm]
    · intro a _
      simpa using ih

theorem length_words_one (alphabet : List α) : (words alphabet 1).length = alphabet.length := by
  rw [length_words]
  simp

theorem length_words_two (alphabet : List α) :
    (words alphabet 2).length = alphabet.length * alphabet.length := by
  rw [length_words]
  simp [Nat.pow_succ]

theorem words_empty_succ (n : Nat) : words ([] : List α) (n + 1) = [] := rfl

theorem length_words_singleton (a : α) (n : Nat) : (words [a] n).length = 1 := by
  rw [length_words]
  simp

end JonnyLean.Combinatorics
