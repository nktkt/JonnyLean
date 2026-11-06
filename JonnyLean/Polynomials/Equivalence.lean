import JonnyLean.Polynomials.Composition

namespace JonnyLean.Polynomials

def Equivalent (p q : Polynomial) : Prop := ∀ x, evaluate p x = evaluate q x

theorem equivalent_refl (p : Polynomial) : Equivalent p p := fun _ => rfl

theorem equivalent_symm (p q : Polynomial) (h : Equivalent p q) : Equivalent q p := fun x => (h x).symm

theorem equivalent_trans (p q r : Polynomial) (h : Equivalent p q) (k : Equivalent q r) :
    Equivalent p r := fun x => (h x).trans (k x)

theorem equivalent_add (p q r s : Polynomial) (h : Equivalent p q) (k : Equivalent r s) :
    Equivalent (add p r) (add q s) := by
  intro x
  simp only [evaluate_add, h x, k x]

theorem equivalent_multiply (p q r s : Polynomial) (h : Equivalent p q) (k : Equivalent r s) :
    Equivalent (multiply p r) (multiply q s) := by
  intro x
  simp only [evaluate_multiply, h x, k x]

theorem equivalent_compose (p q r s : Polynomial) (h : Equivalent p q) (k : Equivalent r s) :
    Equivalent (compose p r) (compose q s) := by
  intro x
  rw [evaluate_compose, evaluate_compose, k x]
  exact h _

theorem equivalent_trailing_zero (p : Polynomial) : Equivalent (p++[0]) p := evaluate_append_zero p

end JonnyLean.Polynomials
