import JonnyLean.Algebra.OddSum

/- Independent, named contract for JL-018. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL018

def sumSpec (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumSpec f n + f n

theorem sum_matches (f : Nat → Nat) (n : Nat) : sumSpec f n = JonnyLean.rangeSum f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumSpec, JonnyLean.rangeSum, ih]

/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ a n : Nat, sumSpec (fun i => 2 * (a + i) + 1) n = 2 * a * n + n ^ 2 :=
  by
  intro a n
  simpa only [sum_matches] using JonnyLean.sum_odd_interval a n

theorem empty_odds : sumSpec (fun i => 2 * (9 + i) + 1) 0 = 0 := rfl

theorem initial_odds : sumSpec (fun i => 2 * i + 1) 5 = 25 := rfl

theorem shifted_odds : sumSpec (fun i => 2 * (3 + i) + 1) 4 = 40 := rfl

end JonnyLean.Contracts.JL018

#print axioms JonnyLean.sum_odd_interval
#print axioms JonnyLean.Contracts.JL018.contract
