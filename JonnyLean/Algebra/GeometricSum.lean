import JonnyLean.Algebra.SumLinearity
import JonnyLean.Algebra.SumIntervals

namespace JonnyLean

/-- A finite geometric sum, including the empty sum and base zero. -/
def geometricSum (a n : Nat) : Nat := rangeSum (fun i => a ^ i) n

theorem geometric_sum_one (n : Nat) : geometricSum 1 n = n := by
  unfold geometricSum
  simpa using range_sum_constant 1 n

theorem geometric_sum_recurrence (a n : Nat) :
    geometricSum a (n + 1) = 1 + a * geometricSum a n := by
  unfold geometricSum
  rw [← range_sum_shift_one, ← range_sum_mul_left]
  congr 1
  apply range_sum_congr
  intro i _
  rw [Nat.pow_succ, Nat.mul_comm]

theorem geometric_sum_formula (a n : Nat) :
    a * geometricSum a n + 1 = geometricSum a n + a ^ n := by
  have h := geometric_sum_recurrence a n
  change geometricSum a n + a ^ n = 1 + a * geometricSum a n at h
  omega

theorem geometric_sum_split (a m n : Nat) :
    geometricSum a (m + n) = geometricSum a m + a ^ m * geometricSum a n := by
  unfold geometricSum
  rw [range_sum_split, ← range_sum_mul_left]
  congr 1
  apply range_sum_congr
  intro i _
  exact Nat.pow_add a m i

theorem geometric_sum_mono_base (a b n : Nat) (h : a ≤ b) :
    geometricSum a n ≤ geometricSum b n := by
  apply range_sum_mono
  intro i _
  exact Nat.pow_le_pow_left h i

theorem geometric_sum_sub_formula (a n : Nat) (ha : 0 < a) :
    (a - 1) * geometricSum a n = a ^ n - 1 := by
  have h := geometric_sum_formula a n
  have ha' : a = (a - 1) + 1 := by omega
  have hmul : a * geometricSum a n = (a - 1) * geometricSum a n + geometricSum a n := by
    calc
      a * geometricSum a n = ((a - 1) + 1) * geometricSum a n := by
        exact congrArg (fun x => x * geometricSum a n) ha'
      _ = (a - 1) * geometricSum a n + geometricSum a n := by rw [Nat.add_mul, Nat.one_mul]
  omega

end JonnyLean
