import JonnyLean.Algebra.FiniteSum

namespace JonnyLean

theorem range_sum_split (f : Nat → Nat) (m n : Nat) :
    rangeSum f (m + n) = rangeSum f m + rangeSum (fun i => f (m + i)) n := by
  induction n with
  | zero => simp [rangeSum]
  | succ n ih =>
    rw [Nat.add_succ]
    simp only [rangeSum, ih]
    omega

theorem range_sum_tail (f : Nat → Nat) (m n : Nat) :
    rangeSum (fun i => f (m + i)) n = rangeSum f (m + n) - rangeSum f m := by
  rw [range_sum_split]
  omega

theorem range_sum_split_three (f : Nat → Nat) (a b c : Nat) :
    rangeSum f (a + b + c) = rangeSum f a + rangeSum (fun i => f (a + i)) b +
      rangeSum (fun i => f (a + b + i)) c := by
  rw [range_sum_split f (a + b) c, range_sum_split f a b]

theorem range_sum_middle (f : Nat → Nat) (m n : Nat) :
    rangeSum f (m + 1 + n) = rangeSum f m + f m +
      rangeSum (fun i => f (m + 1 + i)) n := by
  rw [range_sum_split f (m + 1) n]
  rfl

theorem range_sum_shift_one (f : Nat → Nat) (n : Nat) :
    f 0 + rangeSum (fun i => f (i + 1)) n = rangeSum f (n + 1) := by
  rw [Nat.add_comm n 1, range_sum_split f 1 n]
  simp only [rangeSum, Nat.zero_add]
  congr 1
  apply range_sum_congr
  intro i _
  rw [Nat.add_comm]

end JonnyLean
