import JonnyLean.Algebra.FiniteSum

/- Independent, named contract for JL-015. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL015

def sumSpec (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumSpec f n + f n

theorem sum_matches (f : Nat → Nat) (n : Nat) : sumSpec f n = JonnyLean.rangeSum f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumSpec, JonnyLean.rangeSum, ih]

/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ (f : Nat → Nat) (n : Nat), sumSpec f n = 0 ↔ ∀ i : Nat, i < n → f i = 0 :=
  by
  intro f n
  simpa only [sum_matches] using JonnyLean.range_sum_eq_zero_iff f n

theorem empty_sum : sumSpec (fun i => i + 100) 0 = 0 := rfl

theorem all_zero : sumSpec (fun _ => 0) 5 = 0 := rfl

theorem nonzero_term : sumSpec (fun i => i) 3 = 3 := rfl

end JonnyLean.Contracts.JL015

#print axioms JonnyLean.range_sum_eq_zero_iff
#print axioms JonnyLean.Contracts.JL015.contract
