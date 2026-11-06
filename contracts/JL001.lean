import JonnyLean.NumberTheory.Parity

/-
This contract states the expected proposition without using JonnyLean.Even.
Assigning the named theorem to this exact type checks its arguments,
assumptions, conclusion, and the definitional meaning of Even.
-/
theorem JL001Contract.target :
    ∀ (a b : Nat),
      (∃ ka : Nat, a = 2 * ka) →
      (∃ kb : Nat, b = 2 * kb) →
      ∃ k : Nat, a + b = 2 * k :=
  JonnyLean.even_add

-- Zero is included among the natural numbers and among the even numbers.
example : JonnyLean.Even 0 := ⟨0, rfl⟩

example : ∃ k : Nat, 0 + 0 = 2 * k :=
  JonnyLean.even_add 0 0 ⟨0, rfl⟩ ⟨0, rfl⟩

example : ∃ k : Nat, 0 + 4 = 2 * k :=
  JonnyLean.even_add 0 4 ⟨0, rfl⟩ ⟨2, rfl⟩

example : ∃ k : Nat, 2 + 4 = 2 * k :=
  JonnyLean.even_add 2 4 ⟨1, rfl⟩ ⟨2, rfl⟩

-- Print the dependencies of the theorem as part of the contract report.
#print axioms JonnyLean.even_add
#print axioms JL001Contract.target
