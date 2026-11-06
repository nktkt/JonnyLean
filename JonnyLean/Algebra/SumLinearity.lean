import JonnyLean.Algebra.FiniteSum

namespace JonnyLean

theorem range_sum_add (f g : Nat → Nat) (n : Nat) :
    rangeSum (fun i => f i + g i) n = rangeSum f n + rangeSum g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rangeSum, ih]; omega

theorem range_sum_mul_left (f : Nat → Nat) (c n : Nat) :
    rangeSum (fun i => c * f i) n = c * rangeSum f n := by
  induction n with
  | zero => simp [rangeSum]
  | succ n ih => simp only [rangeSum, ih, Nat.mul_add]

theorem range_sum_mul_right (f : Nat → Nat) (c n : Nat) :
    rangeSum (fun i => f i * c) n = rangeSum f n * c := by
  simp only [Nat.mul_comm, range_sum_mul_left]

theorem range_sum_linear_combination (f g : Nat → Nat) (a b n : Nat) :
    rangeSum (fun i => a * f i + b * g i) n = a * rangeSum f n + b * rangeSum g n := by
  rw [range_sum_add, range_sum_mul_left, range_sum_mul_left]

theorem range_sum_sub (f g : Nat → Nat) (n : Nat)
    (h : ∀ i, i < n → g i ≤ f i) :
    rangeSum (fun i => f i - g i) n = rangeSum f n - rangeSum g n := by
  have heq : rangeSum (fun i => f i - g i) n + rangeSum g n = rangeSum f n := by
    rw [← range_sum_add]
    apply range_sum_congr
    intro i hi
    exact Nat.sub_add_cancel (h i hi)
  omega

theorem range_sum_complement (f g : Nat → Nat) (n c : Nat)
    (h : ∀ i, i < n → f i + g i = c) : rangeSum f n + rangeSum g n = n * c := by
  rw [← range_sum_add, ← range_sum_constant]
  exact range_sum_congr (fun i => f i + g i) (fun _ => c) n h

end JonnyLean
