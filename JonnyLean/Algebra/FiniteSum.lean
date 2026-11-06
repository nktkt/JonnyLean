import Std

namespace JonnyLean

/-- The sum of f(0), ..., f(n-1); there are exactly n terms. -/
def rangeSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rangeSum f n + f n

theorem range_sum_congr (f g : Nat → Nat) (n : Nat)
    (h : ∀ i, i < n → f i = g i) : rangeSum f n = rangeSum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rangeSum]
    rw [ih (by intro i hi; exact h i (by omega)), h n (by omega)]

theorem range_sum_mono (f g : Nat → Nat) (n : Nat)
    (h : ∀ i, i < n → f i ≤ g i) : rangeSum f n ≤ rangeSum g n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    exact Nat.add_le_add (ih (by intro i hi; exact h i (by omega))) (h n (by omega))

theorem range_sum_constant (c n : Nat) : rangeSum (fun _ => c) n = n * c := by
  induction n with
  | zero => simp [rangeSum]
  | succ n ih => simp only [rangeSum, ih, Nat.add_mul, Nat.one_mul]

theorem range_sum_le_bound (f : Nat → Nat) (n c : Nat)
    (h : ∀ i, i < n → f i ≤ c) : rangeSum f n ≤ n * c := by
  rw [← range_sum_constant]
  exact range_sum_mono f (fun _ => c) n h

theorem range_sum_eq_zero_iff (f : Nat → Nat) (n : Nat) :
    rangeSum f n = 0 ↔ ∀ i, i < n → f i = 0 := by
  induction n with
  | zero => simp [rangeSum]
  | succ n ih =>
    constructor
    · intro h i hi
      change rangeSum f n + f n = 0 at h
      have hsum : rangeSum f n = 0 := by omega
      by_cases hin : i < n
      · exact ih.mp hsum i hin
      · have heq : i = n := by omega
        subst i
        omega
    · intro h
      have hsum : rangeSum f n = 0 := ih.mpr (by intro i hi; exact h i (by omega))
      change rangeSum f n + f n = 0
      rw [hsum, h n (by omega)]

theorem range_sum_prefix_le (f : Nat → Nat) (m n : Nat) (h : m ≤ n) :
    rangeSum f m ≤ rangeSum f n := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact Nat.le_refl _
  | succ n ih =>
    by_cases hm : m ≤ n
    · exact Nat.le_trans (ih hm) (Nat.le_add_right _ _)
    · have heq : m = n + 1 := by omega
      subst m
      exact Nat.le_refl _

end JonnyLean
