import JonnyLean.Algebra.SumLinearity

/- Independent, named contract for JL-016. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL016

def sumSpec (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumSpec f n + f n

theorem sum_matches (f : Nat → Nat) (n : Nat) : sumSpec f n = JonnyLean.rangeSum f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumSpec, JonnyLean.rangeSum, ih]

/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ (f g : Nat → Nat) (a b n : Nat), sumSpec (fun i => a * f i + b * g i) n = a * sumSpec f n + b * sumSpec g n :=
  by
  intro f g a b n
  simpa only [sum_matches] using JonnyLean.range_sum_linear_combination f g a b n

theorem empty_combination : sumSpec (fun i => 3 * i + 5 * (i + 1)) 0 = 0 := rfl

theorem concrete_combination : sumSpec (fun i => 2 * i + 3 * (i + 1)) 4 = 42 := rfl

end JonnyLean.Contracts.JL016

#print axioms JonnyLean.range_sum_linear_combination
#print axioms JonnyLean.Contracts.JL016.contract
