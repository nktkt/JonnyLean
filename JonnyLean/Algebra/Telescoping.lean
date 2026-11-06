import JonnyLean.Algebra.FiniteSum

namespace JonnyLean

theorem telescoping_sum (f : Nat → Nat) (n : Nat)
    (h : ∀ i, i < n → f i ≤ f (i + 1)) :
    rangeSum (fun i => f (i + 1) - f i) n + f 0 = f n := by
  induction n with
  | zero => simp [rangeSum]
  | succ n ih =>
    have hprev := ih (by intro i hi; exact h i (by omega))
    have hstep := h n (by omega)
    change (rangeSum (fun i => f (i + 1) - f i) n + (f (n + 1) - f n)) + f 0 = f (n + 1)
    omega

theorem telescoping_sub (f : Nat → Nat) (n : Nat)
    (h : ∀ i, i < n → f i ≤ f (i + 1)) :
    rangeSum (fun i => f (i + 1) - f i) n = f n - f 0 := by
  have heq := telescoping_sum f n h
  omega

theorem telescoping_interval (f : Nat → Nat) (a n : Nat)
    (h : ∀ i, i < n → f (a + i) ≤ f (a + i + 1)) :
    rangeSum (fun i => f (a + i + 1) - f (a + i)) n + f a = f (a + n) := by
  have h' := telescoping_sum (fun i => f (a + i)) n (by
    intro i hi
    simpa only [Nat.add_assoc] using h i hi)
  simpa only [Nat.add_zero, Nat.add_assoc] using h'

theorem constant_increment_formula (f : Nat → Nat) (c n : Nat)
    (h : ∀ i, i < n → f (i + 1) = f i + c) : f n = f 0 + n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [h n (by omega), ih (by intro i hi; exact h i (by omega)), Nat.add_mul, Nat.one_mul]
    omega

theorem bounded_increment_formula (f : Nat → Nat) (c n : Nat)
    (h : ∀ i, i < n → f (i + 1) ≤ f i + c) : f n ≤ f 0 + n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (by intro i hi; exact h i (by omega))
    have hstep := h n (by omega)
    rw [Nat.add_mul, Nat.one_mul]
    omega

end JonnyLean
