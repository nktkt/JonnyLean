import JonnyLean.Algebra.GeometricSum

/- Independent, named contract for JL-019. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL019

def sumSpec (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumSpec f n + f n

theorem sum_matches (f : Nat → Nat) (n : Nat) : sumSpec f n = JonnyLean.rangeSum f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumSpec, JonnyLean.rangeSum, ih]

/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ a n : Nat, 0 < a → (a - 1) * sumSpec (fun i => a ^ i) n = a ^ n - 1 :=
  by
  intro a n ha
  simpa only [sum_matches, JonnyLean.geometricSum] using JonnyLean.geometric_sum_sub_formula a n ha

theorem empty_geometric : (3 - 1) * sumSpec (fun i => 3 ^ i) 0 = 3 ^ 0 - 1 := rfl

theorem base_one : (1 - 1) * sumSpec (fun i => 1 ^ i) 5 = 1 ^ 5 - 1 := rfl

theorem base_two : (2 - 1) * sumSpec (fun i => 2 ^ i) 4 = 2 ^ 4 - 1 := rfl

end JonnyLean.Contracts.JL019

#print axioms JonnyLean.geometric_sum_sub_formula
#print axioms JonnyLean.Contracts.JL019.contract
