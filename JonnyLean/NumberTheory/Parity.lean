import Init

namespace JonnyLean

/-- A natural number is even when it is twice a natural-number witness. -/
def Even (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

/-- The sum of two even natural numbers is even. -/
theorem even_add (a b : Nat) (ha : Even a) (hb : Even b) : Even (a + b) := by
  cases ha with
  | intro ka hka =>
    cases hb with
    | intro kb hkb =>
      refine ⟨ka + kb, ?_⟩
      calc
        a + b = 2 * ka + 2 * kb := by rw [hka, hkb]
        _ = 2 * (ka + kb) := (Nat.mul_add 2 ka kb).symm

end JonnyLean
