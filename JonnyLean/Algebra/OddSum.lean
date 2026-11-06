import JonnyLean.Algebra.SumLinearity
import JonnyLean.Algebra.Quadratic

namespace JonnyLean

theorem sum_first_odds (n : Nat) : rangeSum (fun i => 2 * i + 1) n = n ^ 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change rangeSum (fun i => 2 * i + 1) n + (2 * n + 1) = (n + 1) ^ 2
    rw [ih, square_succ]
    omega

theorem twice_sum_indices (n : Nat) : 2 * rangeSum (fun i => i) n + n = n ^ 2 := by
  have h := sum_first_odds n
  rw [range_sum_add, range_sum_mul_left, range_sum_constant, Nat.mul_one] at h
  exact h

theorem twice_sum_successors (n : Nat) :
    2 * rangeSum (fun i => i + 1) n = n * (n + 1) := by
  rw [range_sum_add, range_sum_constant, Nat.mul_one, Nat.mul_add]
  have h := twice_sum_indices n
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] at h
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem sum_affine_double (a d n : Nat) :
    2 * rangeSum (fun i => a + d * i) n + d * n = 2 * n * a + d * n ^ 2 := by
  rw [range_sum_add, range_sum_constant, range_sum_mul_left, Nat.mul_add]
  have h := congrArg (fun x => d * x) (twice_sum_indices n)
  simp only [Nat.mul_add] at h
  calc
    2 * (n * a) + 2 * (d * rangeSum (fun i => i) n) + d * n =
        2 * n * a + (d * (2 * rangeSum (fun i => i) n) + d * n) := by ac_rfl
    _ = 2 * n * a + d * n ^ 2 := by rw [h]

theorem sum_odd_interval (a n : Nat) :
    rangeSum (fun i => 2 * (a + i) + 1) n = 2 * a * n + n ^ 2 := by
  calc
    rangeSum (fun i => 2 * (a + i) + 1) n =
        rangeSum (fun i => 2 * a + (2 * i + 1)) n := by
          apply range_sum_congr
          intro i _
          omega
    _ = n * (2 * a) + n ^ 2 := by rw [range_sum_add, range_sum_constant, sum_first_odds]
    _ = 2 * a * n + n ^ 2 := by rw [Nat.mul_comm n]

end JonnyLean
