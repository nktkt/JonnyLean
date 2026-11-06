import JonnyLean.Algebra.Affine

/- Independent, named contract for JL-025. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL025

def sumSpec (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumSpec f n + f n

theorem sum_matches (f : Nat → Nat) (n : Nat) : sumSpec f n = JonnyLean.rangeSum f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumSpec, JonnyLean.rangeSum, ih]

def iterateSpec (a b : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => a * iterateSpec a b n x + b

theorem iterate_matches (a b n x : Nat) :
    iterateSpec a b n x = (JonnyLean.NatAffine.iterate ⟨a, b⟩ n).eval x := by
  induction n with
  | zero => simp [iterateSpec, JonnyLean.NatAffine.iterate, JonnyLean.NatAffine.identity, JonnyLean.NatAffine.eval]
  | succ n ih =>
    simp only [iterateSpec, JonnyLean.NatAffine.iterate, JonnyLean.NatAffine.eval_compose]
    change a * iterateSpec a b n x + b = a * (JonnyLean.NatAffine.iterate ⟨a, b⟩ n).eval x + b
    rw [ih]

/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ a b n x : Nat, iterateSpec a b n x = a ^ n * x + b * sumSpec (fun i => a ^ i) n :=
  by
  intro a b n x
  rw [iterate_matches, sum_matches]
  exact JonnyLean.NatAffine.iterate_formula ⟨a, b⟩ n x

theorem zero_iterations : iterateSpec 3 4 0 7 = 7 := rfl

theorem constant_map : iterateSpec 0 5 3 8 = 5 := rfl

theorem translation : iterateSpec 1 3 4 2 = 14 := rfl

theorem affine_example : iterateSpec 2 1 4 3 = 63 := rfl

end JonnyLean.Contracts.JL025

#print axioms JonnyLean.NatAffine.iterate_formula
#print axioms JonnyLean.Contracts.JL025.contract
