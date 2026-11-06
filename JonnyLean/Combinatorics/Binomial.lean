import JonnyLean.Combinatorics.Selections

namespace JonnyLean.Combinatorics

/-- Pascal's recurrence, with out-of-range values equal to zero. -/
def binomial : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binomial n k + binomial n (k + 1)

@[simp] theorem binomial_zero (n : Nat) : binomial n 0 = 1 := by cases n <;> rfl
@[simp] theorem binomial_zero_succ (k : Nat) : binomial 0 (k + 1) = 0 := rfl
theorem binomial_pascal (n k : Nat) : binomial (n + 1) (k + 1) = binomial n k + binomial n (k + 1) := rfl

/-- The recurrence counts selections of positions, even if values repeat. -/
theorem length_selections (xs : List α) (k : Nat) :
    (selections k xs).length = binomial xs.length k := by
  induction xs generalizing k with
  | nil => cases k <;> rfl
  | cons a xs ih =>
    cases k with
    | zero => rfl
    | succ k => simp only [selections_cons_succ, List.length_append, List.length_map,
        List.length_cons, binomial_pascal, ih]

theorem binomial_above (n k : Nat) (h : n < k) : binomial n k = 0 := by
  have hc := length_selections (List.replicate n ()) k
  rw [List.length_replicate] at hc
  rw [selections_too_many _ k (by simpa using h)] at hc
  exact hc.symm

theorem binomial_diagonal (n : Nat) : binomial n n = 1 := by
  have hc := length_selections (List.replicate n ()) n
  rw [List.length_replicate] at hc
  have hs := selections_full (List.replicate n ())
  rw [List.length_replicate] at hs
  rw [hs] at hc
  exact hc.symm

theorem binomial_one (n : Nat) : binomial n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [binomial_pascal, ih, Nat.add_comm]

end JonnyLean.Combinatorics
