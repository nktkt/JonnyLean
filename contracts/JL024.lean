import JonnyLean.Algebra.Telescoping

/- Independent, named contract for JL-024. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL024

def sumSpec (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumSpec f n + f n

theorem sum_matches (f : Nat → Nat) (n : Nat) : sumSpec f n = JonnyLean.rangeSum f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumSpec, JonnyLean.rangeSum, ih]

/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ (f : Nat → Nat) (n : Nat), (∀ i : Nat, i < n → f i ≤ f (i + 1)) → sumSpec (fun i => f (i + 1) - f i) n + f 0 = f n :=
  by
  intro f n h
  simpa only [sum_matches] using JonnyLean.telescoping_sum f n h

theorem empty_differences : sumSpec (fun i => (i + 1) - i) 0 + 0 = 0 := rfl

theorem constant_sequence : sumSpec (fun _ => (7 : Nat) - 7) 4 + 7 = 7 := rfl

theorem square_differences : sumSpec (fun i => (i + 1) ^ 2 - i ^ 2) 4 = 16 := rfl

end JonnyLean.Contracts.JL024

#print axioms JonnyLean.telescoping_sum
#print axioms JonnyLean.Contracts.JL024.contract
