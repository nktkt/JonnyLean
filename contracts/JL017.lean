import JonnyLean.Algebra.SumIntervals

/- Independent, named contract for JL-017. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL017

def sumSpec (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumSpec f n + f n

theorem sum_matches (f : Nat → Nat) (n : Nat) : sumSpec f n = JonnyLean.rangeSum f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumSpec, JonnyLean.rangeSum, ih]

/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ (f : Nat → Nat) (m n : Nat), sumSpec f (m + n) = sumSpec f m + sumSpec (fun i => f (m + i)) n :=
  by
  intro f m n
  simpa only [sum_matches] using JonnyLean.range_sum_split f m n

theorem empty_prefix : sumSpec (fun i => i + 1) (0 + 3) = sumSpec (fun i => i + 1) 0 + sumSpec (fun i => (0 + i) + 1) 3 := rfl

theorem empty_tail : sumSpec (fun i => i + 1) (3 + 0) = sumSpec (fun i => i + 1) 3 + sumSpec (fun i => (3 + i) + 1) 0 := rfl

theorem split_example : sumSpec (fun i => i) 5 = sumSpec (fun i => i) 2 + sumSpec (fun i => 2 + i) 3 := rfl

end JonnyLean.Contracts.JL017

#print axioms JonnyLean.range_sum_split
#print axioms JonnyLean.Contracts.JL017.contract
